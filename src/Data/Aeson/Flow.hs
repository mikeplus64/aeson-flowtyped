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
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
module Data.Aeson.Flow where
import           Control.Lens.Plated
import qualified Data.Aeson             as A
import           Data.Aeson.Types       (Options (..), SumEncoding (..),
                                         defaultOptions)
import qualified Data.ByteString.Lazy   as BL
import           Data.Foldable
import           Data.Function
import           Data.Functor.Classes
import           Data.Functor.Foldable
import           Data.HashMap.Strict    (HashMap)
import qualified Data.HashMap.Strict    as H
import           Data.List              (intersperse)
import           Data.Monoid            hiding (Alt, Any, Sum)
import           Data.Proxy
import           Data.Reflection
import           Data.Text              (Text)
import qualified Data.Text              as T
import qualified Data.Text.Encoding     as T
import qualified Data.Text.Lazy         as TL
import qualified Data.Text.Lazy.Builder as TLB
import           Data.Type.Equality
import           Data.Vector            (Vector)
import qualified Data.Vector            as V
import           GHC.Generics
import           GHC.TypeLits
import           Debug.Trace

inj :: Proxy s -> a -> Inj s a
inj _ = Inj
newtype Inj s a = Inj a
instance Reifies s (Int -> a -> ShowS) => Show (Inj s a) where
  showsPrec i (Inj a) = reflect (Proxy :: Proxy s) i a

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
  | Poly !Var !(Vector a)
  | PolyVar !Var
  deriving (Show, Eq, Functor, Traversable, Foldable, Generic)

data Showy f a = forall s. Reifies s (Int -> a -> ShowS) => Showy (f (Inj s a))

instance Show1 (Showy FlowTypeF) where
  liftShowsPrec _ _ i (Showy a) = showsPrec i a

instance Show1 FlowTypeF where
  liftShowsPrec sp sl i a =
    liftShowsPrec sp sl i (reify sp (\p -> Showy (fmap (inj p) a)))

type FlowType = Fix FlowTypeF

instance Plated FlowType where
  plate f (Fix a) = Fix <$> traverse f a

encodeFlowType :: FlowType -> TL.Text
encodeFlowType = TLB.toLazyText . go
  where
    go :: FlowType -> TLB.Builder
    go (Fix t) = case t of
      Object objAttrs ->
        wrap "{" "}" . comma
        . map (\(name, ftype) -> ft name <> ": " <> go ftype)
        . H.toList
        $! objAttrs
      Map objMapAttrs ->
        wrap "{" "}" . comma . V.toList
        . V.map (\(name, ftype) -> wrap "[" "]" $! ft name <> ": " <> go ftype)
        $! objMapAttrs
      Array elemType -> "Array<" <> go elemType <> ">"
      Tuple tupTypes -> wrap "[" "]" . comma . V.map go $! tupTypes
      Poly name applic -> ft (varName name) <> wrap "<" ">" (comma (V.map go applic))
      PolyVar name -> ft (varName name)
      Alt a b -> go a <> "|" <> go b
      Fun argTypes returnType ->
        (wrap "(" ")"
         . comma
         . V.map (\(name, ftype) -> ft name <> ": " <> go ftype)
         $! argTypes) <> " => " <> go returnType
      Prim pt -> case pt of
        String -> "string"
        Boolean -> "boolean"
        Number -> "number"
        Any -> "any"
        Void -> "void"
      Tag tag -> go (Fix (Literal (A.String tag)))
      Nullable t' -> "?" <> go t'
      Literal v -> ft . T.decodeUtf8 . BL.toStrict . A.encode $! v

    {-# INLINE ft #-}
    ft :: Text -> TLB.Builder
    ft = TLB.fromText

    {-# INLINE comma #-}
    comma :: Foldable f => f TLB.Builder -> TLB.Builder
    comma = mconcat . intersperse ", " . toList

    {-# INLINE wrap #-}
    wrap :: TLB.Builder -> TLB.Builder -> TLB.Builder -> TLB.Builder
    wrap start end = \mid -> start <> mid <> end

cleanUp :: Options -> FlowType -> FlowType
cleanUp opts ft
  = ft
  & bool (allNullaryToStringTag opts && allNullaryObjs ft) makeNullaryStringTags
  where
    bool True  f x = f x
    bool False _ x = x

allNullaryObjs :: FlowType -> Bool
allNullaryObjs ft = case unfix ft of
  Alt a b -> allNullaryObjs a && allNullaryObjs b
  Object o | H.size o == 2 -> case (,)
                                   <$> H.lookup "tag" o
                                   <*> H.lookup "contents" o of
    Just (Fix (Tag _), Fix (Prim Void)) -> True
    _                                   -> False
  _ -> False


makeNullaryStringTags :: FlowType -> FlowType
makeNullaryStringTags (Fix a) = Fix $ case trace ("DO " ++ show a ++ "\n") a of
  Object o -> case H.lookup "tag" o of
    Just (Fix (Tag t)) -> Literal (A.String t)
    _                  -> a
  _ -> a

class KnownBool (a :: Bool) where truth :: Either (a :~: 'True) (a :~: 'False)
instance KnownBool 'True where truth = Left Refl
instance KnownBool 'False where truth = Right Refl

class FlowTyped a where
  flowType :: Options -> Proxy a -> (Text, FlowType)
  default flowType :: (Generic a, GFlowTyped (Rep a))
                   => Options
                   -> Proxy a
                   -> (Text, FlowType)
  flowType opts p = cleanUp opts <$> gflowType opts (fmap from p)

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
      next = gflowRecordFields opt (Proxy :: Proxy (r x))
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
      next@(Fix n) = gflowVal opt (Proxy :: Proxy (r x))
      tagName = gconstrName opt p

instance (GFlowVal a, GFlowVal b) => GFlowVal (a :+: b) where
  gflowVal opt _ = Fix $ Alt
    (gflowVal opt (Proxy :: Proxy (a x)))
    (gflowVal opt (Proxy :: Proxy (b x)))

instance GFlowVal U1 where
  gflowVal _ _ = Fix (Prim Void)

class GFlowRecord a where
  gflowRecordFields :: Options -> Proxy (a x) -> HashMap Text FlowType

instance (KnownSymbol fieldName, GFlowVal ty) =>
         GFlowRecord (S1 ('MetaSel ('Just fieldName) su ss ds) ty) where
  gflowRecordFields opt p = H.singleton
    (gfieldName opt p)
    (gflowVal opt (Proxy :: Proxy (ty x)))

data A = A | B | C
  deriving (Generic, FlowTyped, A.ToJSON)

thing () = flowType defaultOptions (Proxy :: Proxy A)

{-

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

