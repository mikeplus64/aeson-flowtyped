{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE DefaultSignatures         #-}
{-# LANGUAGE DeriveAnyClass            #-}
{-# LANGUAGE DeriveFoldable            #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE DeriveTraversable         #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE InstanceSigs              #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeInType                #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}
module Data.Aeson.Flow
  ( FlowTyped (..)
  , FlowType
  , FlowName (..)
  , FlowTypeF (..)
  , PrimType (..)
  , Fix (..)
  , Var (..)
  , exportFlowTypeAs
  , showFlowType
  , dependencies
  , GFlowTyped
  , deriveFlow
  ) where
import           Control.Applicative
import qualified Data.Aeson              as A
import           Data.Aeson.Types        (Options (..), SumEncoding (..))
import           Data.Fixed              (Fixed)
import           Data.Foldable
import           Data.Functor.Classes
import           Data.Functor.Foldable   hiding (fold)
import           Data.HashMap.Strict     (HashMap)
import qualified Data.HashMap.Strict     as H
import           Data.Int
import           Data.Maybe
import           Data.Proxy
import           Data.Reflection
import           Data.Scientific         (Scientific)
import qualified Data.Set                as Set
import           Data.Text               (Text)
import qualified Data.Text               as T
import qualified Data.Text.Lazy          as TL
import           Data.Time               (UTCTime)
import           Data.Typeable
import           Data.Vector             (Vector)
import qualified Data.Vector             as V
import qualified Data.Vector.Storable    as VS
import qualified Data.Vector.Unboxed     as VU
import qualified Data.Void               as Void
import           Data.Word
import           GHC.Generics
import           GHC.TypeLits
import qualified Text.PrettyPrint.Leijen as PP

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
  | Mixed
  | Any
  deriving (Show, Read, Eq, Ord)

newtype Var = Var { varName :: Text }
  deriving (Show, Read, Eq, Ord)

data FlowName where
  FlowName :: (Typeable a, FlowTyped a) => Proxy a -> Text -> FlowName

instance Show FlowName where
  show (FlowName _ t) = show t

instance Eq FlowName where
  FlowName pa _ == FlowName pb _ = typeOf pa == typeOf pb

instance Ord FlowName where
  FlowName pa _ `compare` FlowName pb _ = compare (typeOf pa) (typeOf pb)

data FlowTypeF a
  = Object !(HashMap Text a)
  | ExactObject !(HashMap Text a)
  | Map !(Vector (Text, a))
  | Array a
  | Tuple !(Vector a)
  | Fun !(Vector (Text, a)) a
  | Alt a a
  | Prim !PrimType
  | Nullable a
  | Literal !A.Value
  | Tag !Text
  | Name !FlowName
  | Poly !Var !(Vector a)
  | PolyVar !Var
  deriving (Show, Eq, Functor, Traversable, Foldable)
-- XXX: vector >= 0.12 has Eq1 vector which allows us to derive eq

instance Show1 FlowTypeF where
  liftShowsPrec sp sl i a =
    liftShowsPrec sp sl i (reify sp (\p -> Showy (fmap (inj p) a)))

type FlowType = Fix FlowTypeF

text :: Text -> PP.Doc
text = PP.text . T.unpack

ppAlts :: [FlowType] -> FlowType -> PP.Doc
ppAlts alts (Fix f) = case f of
  Alt a b -> ppAlts (a:alts) b
  x       -> PP.align
             (sep
              (map pp
               (reverse (Fix x:alts))))
  where
    sep [x]    = x
    sep (x:xs) = x PP.<+> PP.string "|" PP.<$> sep xs
    sep _      = PP.empty


braceList :: [PP.Doc] -> PP.Doc
braceList =
  (\s -> PP.lbrace PP.</> s PP.</> PP.rbrace)
  . PP.align
  . PP.sep
  . PP.punctuate PP.comma

braceBarList :: [PP.Doc] -> PP.Doc
braceBarList =
  (\s -> PP.text "{|" PP.</> s PP.</> PP.text "|}")
  . PP.align
  . PP.sep
  . PP.punctuate PP.comma

ppJson :: A.Value -> PP.Doc
ppJson v = case v of
  A.Array a  -> PP.list (map ppJson (V.toList a))
  A.String t -> PP.squotes (text t)
  A.Number n -> PP.string (show n)
  A.Bool t -> if t then PP.string "true" else PP.string "false"
  A.Null -> PP.string "null"
  A.Object obj ->
    braceBarList
    (map
     (\(name, fty) ->
        PP.space PP.<> text name PP.<+> PP.colon PP.<+> ppJson fty PP.<> PP.space)
     (H.toList obj))

mayWrap :: FlowType -> PP.Doc -> PP.Doc
mayWrap (Fix f) x = case f of
  Nullable _ -> PP.parens x
  Alt _ _    -> PP.parens x
  _          -> x

pp :: FlowType -> PP.Doc
pp (Fix ft) = case ft of
  Object hm -> braceList
    (map
     (\(name, fty) ->
        text name PP.<>
        PP.colon PP.<+>
        pp fty)
     (H.toList hm))
  ExactObject hm -> braceBarList
    (map
     (\(name, fty) ->
        text name PP.<>
        PP.colon PP.<+>
        pp fty)
     (H.toList hm))
  Array a -> mayWrap a (pp a) PP.<> PP.string "[]"
  Tuple t -> PP.list (map pp (V.toList t))
  Alt a b -> ppAlts [a] b
  Prim pt -> case pt of
    Boolean -> PP.text "boolean"
    Number  -> PP.text "number"
    String  -> PP.text "string"
    Void    -> PP.text "void"
    Any     -> PP.text "any"
    Mixed   -> PP.text "mixed"
  Nullable a -> PP.char '?' PP.<> pp a
  Literal a -> ppJson a
  Tag t -> PP.squotes (text t)
  Name (FlowName _ t) -> text t
  _ -> PP.string (show ft)

exportFlowTypeAs :: FlowTyped a => Options -> Maybe Text -> Proxy a -> Text
exportFlowTypeAs opts name' p =
  T.pack . render $
  PP.string "export type " PP.<>
  PP.string (T.unpack (fromMaybe
                       (error "no name")
                       (name <|> name'))) PP.<+> PP.string "=" PP.<$>
  PP.indent 2 (pp ft) PP.<> PP.string ";"
  where
    render = ($[]) . PP.displayS . PP.renderPretty 1.0 80
    name = flowTypeName p
    ft = flowType opts p

showFlowType :: FlowType -> Text
showFlowType = T.pack . show . pp

flowTypePreferName :: (Typeable a, FlowTyped a)
                   => Options -> Proxy a -> FlowType
flowTypePreferName opts p = case flowTypeName p of
  Just n  -> Fix (Name (FlowName p n))
  Nothing -> flowType opts p

dependencies :: FlowTyped a => Proxy a -> [FlowName]
dependencies r = Set.toList (cata (\ft -> case ft of
  Name fn | mfn /= Just fn -> Set.singleton fn
  _       -> fold ft) (flowType A.defaultOptions r))
  where
    mfn = FlowName r <$> flowTypeName r

deriveFlow :: (Generic a, GFlowTyped (Rep a)) => Options -> Proxy a -> FlowType
deriveFlow opt p = gflowType opt (fmap from p)

class Typeable a => FlowTyped a where
  flowType :: Options -> Proxy a -> FlowType
  flowTypeName :: Proxy a -> Maybe Text

  isPrim :: Proxy a -> Bool
  isPrim _ = False

  default flowType :: (Generic a, GFlowTyped (Rep a)) => Options -> Proxy a
                   -> FlowType
  flowType opt p = gflowType opt (fmap from p)

  default flowTypeName
    :: (Rep a ~ D1 ('MetaData name mod pkg t) c, KnownSymbol name)
    => Proxy a -> Maybe Text
  flowTypeName p = Just (T.pack (symbolVal (gGetName p)))
    where
      gGetName :: Rep a ~ D1 ('MetaData name mod pkg t) c => Proxy a -> Proxy name
      gGetName _ = Proxy

class GFlowTyped g where
  gflowType :: Options -> Proxy (g x) -> FlowType

class GFlowVal g where
  gflowVal :: Options -> Proxy (g x) -> FlowType

instance (KnownSymbol name, GFlowVal c) =>
         GFlowTyped (D1 ('MetaData name mod pkg t) c) where
  gflowType opt _ = gflowVal opt (Proxy :: Proxy (c x))

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
    TaggedObject tfn _ -> ExactObject $!
      H.insert (T.pack tfn) (Fix (Tag tagName))
      next
    UntaggedValue -> Object next
    ObjectWithSingleField -> ExactObject (H.fromList [(tagName, Fix (Object next))])
    TwoElemArray -> Tuple (V.fromList [Fix (Tag tagName), Fix (Object next)])
    where
      next = gflowRecordFields opt (fmap unM1 p)
      tagName = gconstrName opt p

instance (KnownSymbol conName, GFlowVal r) =>
         GFlowVal (C1 ('MetaCons conName fx 'False) r) where
  gflowVal opt p = Fix $ case sumEncoding opt of
    TaggedObject tfn cfn -> ExactObject (H.fromList
      [ (T.pack tfn, Fix (Tag tagName))
      , (T.pack cfn, next)
      ])
    UntaggedValue -> n
    ObjectWithSingleField -> ExactObject (H.fromList [(tagName, next)])
    TwoElemArray -> Tuple (V.fromList [Fix (Tag tagName), next])
    where
      next@(Fix n) = gflowVal opt (fmap unM1 p)
      tagName = gconstrName opt p

instance GFlowVal f => GFlowVal (M1 i ('MetaSel mj du ds dl) f) where
  gflowVal opt p = gflowVal opt (fmap unM1 p)

instance FlowTyped r => GFlowVal (Rec0 r) where
  gflowVal opt p = case flowTypePreferName opt (fmap unK1 p) of
    ty
      | not (isPrim p'), Just name <- flowTypeName p' -> Fix (Name (FlowName p' name))
      | otherwise -> ty
    where
      p' = fmap unK1 p

instance (GFlowVal a, GFlowVal b) => GFlowVal (a :+: b) where
  gflowVal opt _ = Fix (Alt
                        (gflowVal opt (Proxy :: Proxy (a x)))
                        (gflowVal opt (Proxy :: Proxy (b x))))

instance (GFlowVal a, GFlowVal b) => GFlowVal (a :*: b) where
  gflowVal opt _ =
    case gflowVal opt (Proxy :: Proxy (a x)) of
      Fix (Tuple a) -> case gflowVal opt (Proxy :: Proxy (b x)) of
        Fix (Tuple b) -> Fix (Tuple (a V.++ b))
        b             -> Fix (Tuple (V.snoc a b))
      a -> case gflowVal opt (Proxy :: Proxy (b x)) of
        Fix (Tuple b) -> Fix (Tuple (V.cons a b))
        b             -> Fix (Tuple (V.fromList [a, b]))

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

--------------------------------------------------------------------------------
-- Instances

instance FlowTyped a => FlowTyped [a] where
  flowType opts _ = Fix (Array (flowTypePreferName opts (Proxy :: Proxy a)))
  isPrim _ = True
  flowTypeName _ = Nothing

instance FlowTyped a => FlowTyped (Vector a) where
  flowType opts _ = Fix (Array (flowTypePreferName opts (Proxy :: Proxy a)))
  isPrim _ = True
  flowTypeName _ = Nothing

instance FlowTyped a => FlowTyped (VU.Vector a) where
  flowType opts _ = Fix (Array (flowTypePreferName opts (Proxy :: Proxy a)))
  isPrim _ = True
  flowTypeName _ = Nothing

instance FlowTyped a => FlowTyped (VS.Vector a) where
  flowType opts _ = Fix (Array (flowTypePreferName opts (Proxy :: Proxy a)))
  isPrim _ = True
  flowTypeName _ = Nothing

instance (FlowTyped a, FlowTyped b) => FlowTyped (a, b) where
  flowTypeName _ = Nothing
  flowType opts _ =
    Fix (Tuple (V.fromList [aFt, bFt]))
    where
      aFt = flowTypePreferName opts (Proxy :: Proxy a)
      bFt = flowTypePreferName opts (Proxy :: Proxy b)

instance FlowTyped a => FlowTyped (Maybe a) where
  flowType opts _ = Fix (Nullable (flowTypePreferName opts (Proxy :: Proxy a)))
  isPrim _ = True
  flowTypeName _ = Nothing

instance (FlowTyped a, FlowTyped b) => FlowTyped (Either a b) where
  flowTypeName _ = Nothing
  flowType opts _ = Fix
    (Alt
     (Fix (ExactObject (H.fromList [("Left", aFt)])))
     (Fix (ExactObject (H.fromList [("Right", bFt)]))))
    where
      aFt = flowTypePreferName opts (Proxy :: Proxy a)
      bFt = flowTypePreferName opts (Proxy :: Proxy b)

instance ( FlowTyped a
         , FlowTyped b
         , FlowTyped c
         ) => FlowTyped (a, b, c) where
  flowTypeName _ = Nothing
  flowType opts _ = Fix (Tuple (V.fromList [aFt, bFt, cFt]))
    where
      aFt = flowTypePreferName opts (Proxy :: Proxy a)
      bFt = flowTypePreferName opts (Proxy :: Proxy b)
      cFt = flowTypePreferName opts (Proxy :: Proxy c)

instance FlowTyped Text where
  isPrim  _ = True
  flowType _ _ = Fix (Prim String)
  flowTypeName _ = Nothing

instance FlowTyped TL.Text where
  isPrim  _ = True
  flowType _ _ = Fix (Prim String)
  flowTypeName _ = Nothing

instance {-# OVERLAPS #-} FlowTyped String where
  isPrim  _ = True
  flowType _ _ = Fix (Prim String)
  flowTypeName _ = Nothing

instance FlowTyped Void.Void where
  isPrim  _ = True
  flowType _ _ = Fix (Prim Void)
  flowTypeName _ = Nothing

instance FlowTyped Char where
  isPrim  _ = True
  flowType _ _ = Fix (Prim String)
  flowTypeName _ = Nothing

instance FlowTyped Bool where
  isPrim  _ = True
  flowType _ _ = Fix (Prim Boolean)
  flowTypeName _ = Nothing

instance FlowTyped A.Value where
  isPrim  _ = True
  flowType _ _ = Fix (Prim Mixed)
  flowTypeName _ = Nothing

instance FlowTyped UTCTime where
  isPrim  _ = False
  flowType _ _ = Fix (Prim String)
  flowTypeName _ = Nothing

instance Typeable a => FlowTyped (Fixed a) where
  isPrim  _ = False
  flowType _ _ = Fix (Prim Number)
  flowTypeName _ = Nothing

-- monomorphic numeric instances
$(concat <$> mapM
  (\ty ->
     [d|
      instance FlowTyped $ty where
        isPrim  _ = False
        flowType _ _ = Fix (Prim Number)
        flowTypeName _ = Nothing |])
  [ [t|Int|], [t|Int8|], [t|Int16|], [t|Int32|], [t|Int64|]
  , [t|Word|], [t|Word8|], [t|Word16|], [t|Word32|], [t|Word64|]
  , [t|Float|], [t|Double|], [t|Scientific|]
  ])

