{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLists       #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
module Data.Aeson.Flow where
import           Control.Lens.Plated
import qualified Data.Aeson             as A
import           Data.Aeson.Types       (Options (..), SumEncoding (..))
import           Data.Functor.Classes
import           Data.Functor.Foldable
import           Data.HashMap.Strict    (HashMap)
import qualified Data.HashMap.Strict    as H
import           Data.Proxy
import           Data.Reflection
import qualified Data.Void as Void
import qualified Text.PrettyPrint.Leijen as PP
import           Data.Text              (Text)
import qualified Data.Text              as T
import qualified Data.Text.Lazy         as TL
import           Data.Vector            (Vector)
import qualified Data.Vector            as V
import           GHC.Generics
import           GHC.TypeLits

--------------------------------------------------------------------------------
-- Magical newtype for injecting showsPrec into any arbitrary Show

inj :: Proxy s -> a -> Inj s a
inj _ = Inj
newtype Inj s a = Inj a
-- needs UndecidableInstances
instance Reifies s (Int -> a -> ShowS) => Show (Inj s a) where
  showsPrec i (Inj a) = reflect (Proxy :: Proxy s) i a

data Showy f a = forall s. Reifies s (Int -> a -> ShowS) => Showy (f (Inj s a))
instance Show1 (Showy FlowTypeF) where
  liftShowsPrec _ _ i (Showy a) = showsPrec i a

--------------------------------------------------------------------------------

data PrimType
  = Boolean
  | Number
  | String
  | Void
  | Any
  deriving (Show, Read, Eq, Ord)

newtype Var = Var { varName :: Text }
  deriving (Show, Read, Eq, Ord)

data FlowTypeF a
  = Object !(HashMap Text a)
  | Map !(Vector (Text, a))
  | Array a
  | Tuple !(Vector a)
  | Fun !(Vector (Text, a)) a
  | Alt a a
  | Prim !PrimType
  | Nullable a
  | Literal !A.Value
  | Tag !Text
  | Name !Text
  | Poly !Var !(Vector a)
  | PolyVar !Var
  deriving (Show, Eq, Functor, Traversable, Foldable, Generic)

instance Show1 FlowTypeF where
  liftShowsPrec sp sl i a =
    liftShowsPrec sp sl i (reify sp (\p -> Showy (fmap (inj p) a)))

type FlowType = Fix FlowTypeF

instance Plated FlowType where
  plate f (Fix a) = Fix <$> traverse f a

text :: Text -> PP.Doc
text = PP.text . T.unpack

ppAlts :: [FlowType] -> FlowType -> PP.Doc
ppAlts alts (Fix f) = case f of
  Alt a b -> ppAlts (a:alts) b
  x       -> PP.encloseSep PP.empty PP.empty
             (PP.string "| ")
             (map pp (reverse (Fix x:alts)))

braceList :: [PP.Doc] -> PP.Doc
braceList = PP.encloseSep PP.lbrace PP.rbrace (PP.comma PP.<> PP.space)

ppJson :: A.Value -> PP.Doc
ppJson v = case v of
  A.Array a  -> PP.list (map ppJson (V.toList a))
  A.String t -> PP.squotes (text t)
  A.Number n -> PP.string (show n)
  A.Bool t -> if t then PP.string "true" else PP.string "false"
  A.Null -> PP.string "null"
  A.Object obj ->
    braceList
    (map
     (\(name, fty) -> text name PP.<+> PP.colon PP.<+> ppJson fty)
     (H.toList obj))

pp :: FlowType -> PP.Doc
pp (Fix ft) = case ft of
  Object hm -> braceList
    (map
     (\(name, fty) -> text name PP.<> PP.colon PP.<+> pp fty)
     (H.toList hm))
  Array a -> PP.string "Array" PP.<> PP.angles (pp a)
  Tuple t -> PP.list (map pp (V.toList t))
  Alt a b -> ppAlts [a] b
  Prim pt -> case pt of
    Boolean -> PP.text "boolean"
    Number -> PP.text "number"
    String -> PP.text "string"
    Void -> PP.text "void"
    Any -> PP.text "any"
  Nullable a -> PP.char '?' PP.<> pp a
  Literal a -> ppJson a
  Tag t -> PP.squotes (text t)
  Name t -> text t
  _ -> PP.empty

class FlowTyped a where
  flowType :: Options -> Proxy a -> (Text, FlowType)

  isPrim :: Proxy a -> Bool
  isPrim _ = False

  default flowType :: (Generic a, GFlowTyped (Rep a))
                   => Options
                   -> Proxy a
                   -> (Text, FlowType)
  flowType opt p = gflowType opt (fmap from p)

instance FlowTyped Int where
  isPrim  _ = True
  flowType _ _ = ("Int", Fix (Prim Number))

instance FlowTyped Float where
  isPrim  _ = True
  flowType _ _ = ("Float", Fix (Prim Number))

instance FlowTyped Double where
  isPrim  _ = True
  flowType _ _ = ("Double", Fix (Prim Number))

instance FlowTyped Text where
  isPrim  _ = True
  flowType _ _ = ("String", Fix (Prim String))

instance FlowTyped TL.Text where
  isPrim  _ = True
  flowType _ _ = ("String", Fix (Prim String))

instance FlowTyped String where
  isPrim  _ = True
  flowType _ _ = ("String", Fix (Prim String))

instance FlowTyped Void.Void where
  isPrim  _ = True
  flowType _ _ = ("Void", Fix (Prim Void))

class GFlowTyped g where
  gflowType :: Options -> Proxy (g x) -> (Text, FlowType)

class GFlowVal g where
  gflowVal :: Options -> Proxy (g x) -> FlowType

instance (KnownSymbol name, GFlowVal c) =>
         GFlowTyped (D1 ('MetaData name mod pkg t) c) where
  gflowType opt _ =
    ( T.pack (symbolVal (Proxy :: Proxy name))
    , gflowVal opt (Proxy :: Proxy (c x))
    )

gconstrName :: forall conName fx isRecord r x.
               KnownSymbol conName
            => Options
            -> Proxy (C1 ('MetaCons conName fx isRecord) r x)
            -> Text
gconstrName opt _ =
  T.pack (constructorTagModifier opt (symbolVal (Proxy :: Proxy conName)))

gfieldName :: forall name su ss ds r x.
              KnownSymbol name
           => Options
           -> Proxy (S1 ('MetaSel ('Just name) su ss ds) r x)
           -> Text
gfieldName opt _ =
  T.pack (fieldLabelModifier opt (symbolVal (Proxy :: Proxy name)))

instance (KnownSymbol conName, GFlowRecord r) =>
         GFlowVal (C1 ('MetaCons conName fx 'True) r) where
  gflowVal opt p = Fix $ case sumEncoding opt of
    TaggedObject tfn _ -> Object $!
      H.insert (T.pack tfn) (Fix (Tag tagName))
      next
    UntaggedValue -> Object next
    ObjectWithSingleField -> Object [(tagName, Fix (Object next))]
    TwoElemArray -> Tuple [Fix (Tag tagName), Fix (Object next)]
    where
      next = gflowRecordFields opt (fmap unM1 p)
      tagName = gconstrName opt p

instance (KnownSymbol conName, GFlowVal r) =>
         GFlowVal (C1 ('MetaCons conName fx 'False) r) where
  gflowVal opt p = Fix $ case sumEncoding opt of
    TaggedObject tfn cfn ->
      Object
      [ (T.pack tfn, Fix (Tag tagName))
      , (T.pack cfn, next)
      ]
    UntaggedValue -> n
    ObjectWithSingleField -> Object [(tagName, next)]
    TwoElemArray -> Tuple [Fix (Tag tagName), next]
    where
      next@(Fix n) = gflowVal opt (fmap unM1 p)
      tagName = gconstrName opt p

instance GFlowVal f =>
         GFlowVal (M1 i ('MetaSel mj du ds dl) f) where
  gflowVal opt p = gflowVal opt (fmap unM1 p)

instance FlowTyped r => GFlowVal (Rec0 r) where
  gflowVal opt p = case flowType opt (fmap unK1 p) of
    (name, ty)
      | not (isPrim p') -> Fix (Name name)
      | otherwise       -> ty
    where p' = fmap unK1 p

instance (GFlowVal a, GFlowVal b) => GFlowVal (a :+: b) where
  gflowVal opt _ = Fix (Alt
                        (gflowVal opt (Proxy :: Proxy (a x)))
                        (gflowVal opt (Proxy :: Proxy (b x))))

instance (GFlowVal a, GFlowVal b) => GFlowVal (a :*: b) where
  gflowVal opt _ =
    case gflowVal opt (Proxy :: Proxy (a x)) of
      Fix (Tuple a) -> case gflowVal opt (Proxy :: Proxy (b x)) of
        Fix (Tuple b) -> Fix (Tuple (a V.++ b))
        b -> Fix (Tuple (V.snoc a b))
      a -> case gflowVal opt (Proxy :: Proxy (b x)) of
        Fix (Tuple b) -> Fix (Tuple (V.cons a b))
        b -> Fix (Tuple [a, b])

instance GFlowVal U1 where
  gflowVal _ _ = Fix (Prim Void)

class GFlowRecord a where
  gflowRecordFields :: Options -> Proxy (a x) -> HashMap Text FlowType

instance (KnownSymbol fieldName, GFlowVal ty) =>
         GFlowRecord (S1 ('MetaSel ('Just fieldName) su ss ds) ty) where
  gflowRecordFields opt p = H.singleton
    (gfieldName opt p)
    (gflowVal opt (Proxy :: Proxy (ty x)))

instance (GFlowRecord f, GFlowRecord g) =>
         GFlowRecord (f :*: g) where
  gflowRecordFields opt _ =
    let
      fx = gflowRecordFields opt (Proxy :: Proxy (f x))
      gx = gflowRecordFields opt (Proxy :: Proxy (g x))
    in
      H.union fx gx

{-
data A0 = A1 | B1 | C1
  deriving (Generic, FlowTyped, A.ToJSON)

data A = A A0 String A0 | B { b :: Int, c :: Double } | C Int
  deriving (Generic, FlowTyped, A.ToJSON)

t = flowType defaultOptions (Proxy :: Proxy A)
a = A.genericToJSON defaultOptions{ allNullaryToStringTag = True } (A A1 "a" A1)



>>> data A = A { asdf :: Either Int String } deriving (Generic)
>>> :t from (undefined :: A)
from (undefined :: A)
  :: D1
       ('MetaData "A" "Ghci11" "interactive" 'False)
       (C1
          ('MetaCons "A" 'PrefixI 'True)
          (S1
             ('MetaSel
                ('Just "asdf")
                'NoSourceUnpackedness
                'NoSourceStrictness
                'DecidedLazy)
             (Rec0 (Either Int String))))
       x

>>> data T = T Int | U | V deriving (Generic, A.ToJSON)
>>> :t from (T 3)
from (T 3)
  :: D1
       ('MetaData "T" "Ghci5" "interactive" 'False)
       (C1
          ('MetaCons "T" 'PrefixI 'False)
          (S1
             ('MetaSel
                'Nothing 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy)
             (Rec0 Int))
        :+: (C1 ('MetaCons "U" 'PrefixI 'False) U1
             :+: C1 ('MetaCons "V" 'PrefixI 'False) U1))
       x


>>> data E = E | F | G deriving (Generic, A.ToJSON)
>>> :t from E
from E
  :: D1
       ('MetaData "E" "Ghci9" "interactive" 'False)
       (C1 ('MetaCons "E" 'PrefixI 'False) U1
        :+: (C1 ('MetaCons "F" 'PrefixI 'False) U1
             :+: C1 ('MetaCons "G" 'PrefixI 'False) U1))
       x

-}

