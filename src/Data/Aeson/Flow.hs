{-# LANGUAGE CPP                       #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE DefaultSignatures         #-}
{-# LANGUAGE DeriveAnyClass            #-}
{-# LANGUAGE DeriveFoldable            #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE DeriveTraversable         #-}
{-# LANGUAGE DerivingStrategies        #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE InstanceSigs              #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeInType                #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE ViewPatterns              #-}
-- | Derive <https://flow.org/ Flow types> using aeson 'Options'.
--
-- Does not currently support the 'unwrapUnaryRecords' option.
module Data.Aeson.Flow
  ( -- * AST types
    FlowTyped (..)
  , callType
  , FlowTypeF
  , FlowType
  -- , Fix (..)
  , pattern FObject
  , pattern FExactObject
  , pattern FObjectMap
  , pattern FArray
  , pattern FTuple
  , pattern FFun
  , pattern FAlt
  , pattern FPrim
  , pattern FPrimBoolean
  , pattern FPrimNumber
  , pattern FPrimString
  , pattern FPrimBottom
  , pattern FPrimMixed
  , pattern FPrimUnknown
  , pattern FPrimNull
  , pattern FPrimNever
  , pattern FPrimUndefined
  , pattern FPrimAny
  , pattern FNullable
  , pattern FOmitable
  , pattern FLiteral
  , pattern FTag
  , pattern FName
  , pattern FGenericParam
  , pattern FCallType
    -- * Code generation
    -- ** Wholesale ES6/flow modules
  , Export
  , export
  , RenderMode (..)
  , RenderOptions (..)
  , ModuleOptions (..)
  , typeScriptModuleOptions
  , flowModuleOptions
  , generateModule
  , writeModule
  , showTypeAs
  , exportTypeAs
    -- ** TS specific
  , showTypeScriptType
    -- ** Flow specific
  , showFlowType
    -- * Dependencies
  , exportsDependencies
  , dependencies
    -- * Utility
  , FlowCallable
  , FlowName (..)
  , Flowable (..)
  , FlowTyFields (..)
  , FlowDeconstructField
  , Typeable
  , typeRep
  ) where
import           Control.Monad
import           Control.Monad.State.Strict
import           Control.Monad.Reader
import qualified Data.Aeson                       as A
import           Data.Aeson.Types                 (Options (..),
                                                   SumEncoding (..))
import           Data.Eq.Deriving                 (deriveEq1)
import           Data.Fix                         (Fix (..))
import           Data.Fixed                       (Fixed)
import           Data.Functor.Classes
import           Data.Functor.Compose
import           Data.Functor.Foldable            hiding (fold)
import           Data.HashMap.Strict              (HashMap)
import qualified Data.HashMap.Strict              as H
import qualified Data.HashSet                     as HashSet
import           Data.Int
import qualified Data.IntMap.Strict               as I
import qualified Data.IntSet                      as IntSet
import           Data.Kind                        (Type)
import           Data.List                        (foldl')
import           Data.Map.Strict                  (Map)
import qualified Data.Map.Strict                  as M
import           Data.Maybe
import           Data.Semigroup hiding (Any)
import           Data.Proxy
import           Data.Reflection
import           Data.Scientific                  (Scientific)
import qualified Data.Set                         as Set
import           Data.Text                        (Text)
import qualified Data.Text                        as T
import qualified Data.Text.IO                     as TIO
import qualified Data.Text.Lazy                   as TL
import           Data.Time                        (UTCTime)
import qualified Data.Tree                        as Tree
import           Data.Typeable
import           Data.Vector                      (Vector)
import qualified Data.Vector                      as V
import qualified Data.Vector.Storable             as VS
import qualified Data.Vector.Unboxed              as VU
import qualified Data.Void                        as Void
import           Data.Word
import           GHC.Generics
import           GHC.TypeLits
import qualified Text.PrettyPrint.Leijen          as PP
import qualified Type.Reflection                  as TR

import Debug.Trace

-- | The main AST for flowtypes.
data FlowTypeF a
  = Object !(HashMap Text a)
  | ExactObject !(HashMap Text a)
  | ObjectMap !Text a a
  | Array a
  | Tuple !(Vector a)
  | Fun !(Vector (Text, a)) a
  | Alt a a
  | Prim !PrimType
  | Nullable a
  | Omitable a -- ^ omitable when null or undefined
  | Literal !A.Value
  | Tag !Text
  | GenericParam !Int
  | CallType !FlowName [a]
  | SomeFlowType !Flowable
  deriving (Show, Eq, Functor, Traversable, Foldable)

-- | A primitive flow/javascript type
data PrimType
  = Boolean
  | Number
  | String
  | Null
  | Undefined
  | Bottom -- ^ uninhabited type; @never@ in typescript, and @empty@ in flow
  | Mixed -- ^ @unknown@ in typescript, @mixed@ in flow
  | Any
  deriving (Show, Read, Eq, Ord)

-- | A name for a flowtyped data-type. These are returned by 'dependencies'.
data FlowName where
  FlowName :: (FlowCallable a) => Proxy a -> Text -> FlowName

data Flowable where
  Flowable :: (FlowCallable a) => Proxy a -> Flowable

data Showy f a = forall s. Reifies s (Int -> a -> ShowS) => Showy (f (Inj s a))
instance Show1 (Showy FlowTypeF) where
  liftShowsPrec _ _ i (Showy a) = showsPrec i a


--------------------------------------------------------------------------------
-- Magical newtype for injecting showsPrec into any arbitrary Show

inj :: Proxy s -> a -> Inj s a
inj _ = Inj

newtype Inj s a = Inj a
-- needs UndecidableInstances

instance Reifies s (Int -> a -> ShowS) => Show (Inj s a) where
  showsPrec i (Inj a) = reflect (Proxy :: Proxy s) i a

--------------------------------------------------------------------------------

data RenderMode = RenderTypeScript | RenderFlow
  deriving (Eq, Show)

data RenderOptions = RenderOptions
  { renderMode :: !RenderMode
  } deriving (Eq, Show)

instance Show FlowName where
  show (FlowName _ t) = show t

instance Eq FlowName where
  FlowName (t0 :: Proxy t0) n0 == FlowName (t1 :: Proxy t1) n1 =
    case eqT :: Maybe (t0 :~: t1) of
      Just Refl -> (t0, n0) == (t1, n1)
      Nothing -> False

instance Ord FlowName where
  FlowName t0 n0 `compare` FlowName t1 n1 = n0 `compare` n1
  -- XXX this breaks using (typeRep t0, n0) `compare` (typeRep t1, n1) for some
  -- reason... dunno why

instance Show Flowable where
  show (Flowable t) = show (typeRep t)

instance Eq Flowable where
  Flowable a == Flowable b = typeRep a == typeRep b

instance Ord Flowable where
  Flowable a `compare` Flowable b = typeRep a `compare` typeRep b

-- XXX: vector >= 0.12 has Eq1 vector which allows us to use eq for Fix
-- FlowTypeF and related types

--------------------------------------------------------------------------------

pattern FObject :: HashMap Text FlowType -> FlowType
pattern FObject x = Fix (Object x)

pattern FExactObject :: HashMap Text FlowType -> FlowType
pattern FExactObject x = Fix (ExactObject x)

pattern FObjectMap :: Text -> FlowType -> FlowType -> FlowType
pattern FObjectMap keyName keyType vals = Fix (ObjectMap keyName keyType vals)

pattern FArray :: FlowType -> FlowType
pattern FArray a = Fix (Array a)

pattern FTuple :: Vector FlowType -> FlowType
pattern FTuple a = Fix (Tuple a)

pattern FFun :: Vector (Text, FlowType) -> FlowType -> FlowType
pattern FFun v t = Fix (Fun v t)

pattern FAlt :: FlowType -> FlowType -> FlowType
pattern FAlt a b = Fix (Alt a b)

pattern FPrim :: PrimType -> FlowType
pattern FPrim a = Fix (Prim a)

pattern FPrimBoolean :: FlowType
pattern FPrimBoolean = FPrim Boolean

pattern FPrimNumber :: FlowType
pattern FPrimNumber = FPrim Number

pattern FPrimString :: FlowType
pattern FPrimString = FPrim String

pattern FPrimBottom :: FlowType
pattern FPrimBottom = FPrim Bottom

pattern FPrimMixed :: FlowType
pattern FPrimMixed = FPrim Mixed

pattern FPrimUnknown :: FlowType
pattern FPrimUnknown = FPrim Mixed

pattern FPrimAny :: FlowType
pattern FPrimAny = FPrim Any

pattern FPrimNever :: FlowType
pattern FPrimNever = FPrim Bottom

pattern FPrimNull :: FlowType
pattern FPrimNull = FPrim Null

pattern FPrimUndefined :: FlowType
pattern FPrimUndefined = FPrim Undefined

pattern FNullable :: FlowType -> FlowType
pattern FNullable a = Fix (Nullable a)

pattern FOmitable :: FlowType -> FlowType
pattern FOmitable a = Fix (Omitable a)

pattern FLiteral :: A.Value -> FlowType
pattern FLiteral a = Fix (Literal a)

pattern FTag :: Text -> FlowType
pattern FTag a = Fix (Tag a)

pattern FName :: FlowName -> FlowType
pattern FName a = Fix (CallType a [])

pattern FGenericParam :: Int -> FlowType
pattern FGenericParam a = Fix (GenericParam a)

pattern FCallType :: FlowName -> [FlowType] -> FlowType
pattern FCallType f xs = Fix (CallType f xs)

--------------------------------------------------------------------------------

instance Show1 FlowTypeF where
  liftShowsPrec sp sl i a =
    liftShowsPrec sp sl i (reify sp (\p -> Showy (fmap (inj p) a)))

data GFlowInfo a = Constr !Text GFlowTypeI a | NoInfo a
  deriving (Show, Functor, Traversable, Foldable)

instance Show1 (Showy GFlowInfo) where
  liftShowsPrec _ _ i (Showy a) = showsPrec i a

instance Show1 GFlowInfo where
  liftShowsPrec sp sl i a =
    liftShowsPrec sp sl i (reify sp (\p -> Showy (fmap (inj p) a)))

type GFlowTypeI = Fix (GFlowInfo `Compose` FlowTypeF)

type FlowType = Fix FlowTypeF

text :: Text -> PP.Doc
text = PP.text . T.unpack

squotes :: Text -> PP.Doc
squotes = PP.squotes . text . T.replace "'" "\\'"

type Poly = ReaderT RenderOptions (Reader [Flowable])

ppAlts :: [FlowType] -> FlowType -> Poly PP.Doc
ppAlts alts (Fix f) = case f of
  Alt a b -> ppAlts (a:alts) b
  x       -> PP.align . sep <$> mapM pp (reverse (Fix x:alts))
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
  A.String t -> squotes t
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
  Omitable _ -> PP.parens x
  Alt _ _    -> PP.parens x
  Array _    -> PP.parens x
  _          -> x

ppObject :: HashMap Text FlowType -> Poly [PP.Doc]
ppObject = mapM ppField . H.toList
  where
    ppField (name, fty) = do
      case fty of
        Fix (Omitable fty') ->
          -- key?: type
          (\fty'' -> text name PP.<> PP.text "?" PP.<> PP.colon PP.<+> fty'') <$> pp fty'

        fty' ->
          -- key: type
          (\fty'' -> text name PP.<> PP.colon PP.<+> fty'') <$> pp fty'

polyVarNames :: [Text]
polyVarNames =
  map T.singleton ['A'..'Z'] ++
  zipWith (\i t -> t `T.append` T.pack (show i)) [0 :: Int ..] polyVarNames

pp ::  FlowType -> Poly PP.Doc
pp (Fix ft) = case ft of
  ObjectMap keyName keyType a ->
    (\r -> braceList
      [ PP.brackets (text keyName PP.<> PP.text ": string") PP.<>
        PP.colon PP.<+>
        r
      ]) <$> pp a

  Object hm ->
    braceList <$> ppObject hm

  ExactObject hm -> do
    mode <- asks renderMode
    case mode of
      RenderFlow       -> braceBarList <$> ppObject hm
      RenderTypeScript -> braceList <$> ppObject hm

  -- x[]
  Array a ->
    (\r -> mayWrap a r PP.<> PP.string "[]") <$> pp a

  -- [x, y, z]
  Tuple t ->
    PP.list <$> mapM pp (V.toList t)

  Alt a b ->
    ppAlts [a] b

  Prim pt -> do
    mode <- asks renderMode
    return $ case pt of
      Boolean   -> PP.text "boolean"
      Number    -> PP.text "number"
      String    -> PP.text "string"
      Null      -> PP.text "null"
      Undefined -> PP.text "undefined"
      Any       -> PP.text "any"
      Mixed     -> case mode of
        RenderFlow       -> PP.text "mixed"
        RenderTypeScript -> PP.text "unknown"
      Bottom    -> case mode of
        RenderFlow       -> PP.text "empty"
        RenderTypeScript -> PP.text "never"

  Nullable a ->
    -- n.b. there is no 'undefined' in json. void is undefined | null in both ts
    -- and flow (and ?x syntax for void|x)
    (\a' -> PP.text "null" PP.<+> PP.string "|" PP.<+> a') <$> pp a

  Omitable a ->
    pp (FNullable a)

  Literal a ->
    return (ppJson a)

  Tag t ->
    return (squotes t)

  GenericParam ix -> do
    opts <- ask
    params <- lift ask
    let ft | ix < length params = case params !! ix of
               Flowable p -> callType p
           | otherwise = FPrimNever
    let r = runReaderT (pp ft) opts `runReader` []
    return r

  CallType (FlowName _ t) [] ->
    return (text t)

  CallType (FlowName _ t) args -> do
    vs <- mapM pp args
    return (text t PP.<> PP.angles (PP.hsep (PP.punctuate PP.comma vs)))

  _ ->
    return (PP.string (show ft))

-- | Pretty-print a flowtype in flowtype syntax
renderTypeWithOptions :: RenderOptions -> FlowType -> [Flowable] -> PP.Doc
renderTypeWithOptions opts ft params =
  (pp ft `runReaderT` opts) `runReader` params

-- | Pretty-print a flowtype in flowtype syntax
showFlowType :: FlowType -> [Flowable] -> Text
showFlowType ft params =
  T.pack . show $ renderTypeWithOptions RenderOptions{renderMode=RenderFlow} ft params

-- | Pretty-print a flowtype in flowtype syntax
showTypeScriptType :: FlowType -> [Flowable] -> Text
showTypeScriptType ft params =
  T.pack . show $ renderTypeWithOptions RenderOptions{renderMode=RenderTypeScript} ft params

--------------------------------------------------------------------------------
-- Module exporting

-- | Generate a @ export type @ declaration.
exportTypeAs :: RenderOptions -> Text -> FlowType -> [Flowable] -> Text
exportTypeAs opts = showTypeAs opts True

-- | Generate a @ type @ declaration, possibly an export.
showTypeAs :: RenderOptions -> Bool -> Text -> FlowType -> [Flowable] -> Text
showTypeAs opts isExport name ft params =
  T.pack . render $
  PP.string (if isExport then "export type " else "type ")
  PP.<> text name
  PP.<> renderedParams
  PP.<+> text "="
  PP.<+> PP.indent 2 renderedTypeDecl
  PP.<> text ";"
  PP.<> PP.linebreak
  where
    renderedTypeDecl = renderTypeWithOptions opts ft params
    renderedParams
      | null params = mempty
      | otherwise =
        PP.angles (PP.hsep
                   (PP.punctuate PP.comma
                    (map text (take (length params) polyVarNames))))

    render = ($[]) . PP.displayS . PP.renderPretty 1.0 80

-- | Compute all the dependencies of a 'FlowTyped' thing, including itself.
dependencies :: (FlowCallable a) => Proxy a -> Set.Set FlowName
dependencies p0 =
  (case flowTypeName p0 of
     Just t -> Set.insert (FlowName p0 t)
     Nothing -> id)
  (M.foldl' Set.union Set.empty (transitiveDeps (Flowable p0) M.empty))
  where
    flowNameToFlowable (FlowName fn _) = Flowable fn

    immediateDeps :: FlowType -> Set.Set FlowName
    immediateDeps (FCallType n tys) = Set.insert n (Set.unions (map immediateDeps tys))
    immediateDeps (Fix p)           = foldMap immediateDeps p

    transitiveDeps
      :: Flowable
      -> M.Map Flowable (Set.Set FlowName)
      -> M.Map Flowable (Set.Set FlowName)
    transitiveDeps fpf@(Flowable p) acc
      | fpf `M.notMember` acc =
          let
            imms = immediateDeps (flowType p)
            withThis = M.insert fpf imms acc
          in
            Set.foldr' (\x xs -> transitiveDeps (flowNameToFlowable x) xs) withThis imms
      | otherwise = acc

data ModuleOptions = ModuleOptions
  { -- | You might want to change this to include e.g. flow-runtime
    pragmas       :: [Text]
  , header        :: [Text]
  , exportDeps    :: Bool
  , computeDeps   :: Bool
  , renderOptions :: RenderOptions
  } deriving (Eq, Show)

flowModuleOptions :: ModuleOptions
flowModuleOptions = ModuleOptions
  { pragmas = ["// @flow"]
  , header = ["This module has been generated by aeson-flowtyped."]
  , exportDeps = True
  , computeDeps = True
  , renderOptions = RenderOptions{renderMode = RenderFlow}
  }

typeScriptModuleOptions :: ModuleOptions
typeScriptModuleOptions = ModuleOptions
  { pragmas = []
  , header = ["This module has been generated by aeson-flowtyped."]
  , exportDeps = True
  , computeDeps = True
  , renderOptions = RenderOptions{renderMode = RenderTypeScript}
  }

data Export where
  Export :: (FlowCallable a) => Proxy a -> Export

export :: forall a. (FlowCallable a) => Export
export = Export (Proxy :: Proxy a)

instance Eq Export where
  Export p0 == Export p1 =
    flowTypeName p0 == flowTypeName p1 ||
    typeRep p0 == typeRep p1

exportsDependencies :: [Export] -> Set.Set FlowName
exportsDependencies = foldMap $ \e -> case e of
  Export a -> dependencies a

generateModule :: ModuleOptions -> [Export] -> Text
generateModule opts exports = T.unlines $
  (\m -> (pragmas opts ++ map ("// " `T.append`) (header opts)) ++
         (T.empty : m))
  . map flowDecl
  . flowNames
  $ exports
  where
    flowNames =
      if computeDeps opts
      then Set.toList . exportsDependencies
      else catMaybes . map (\ex -> case ex of
        Export p -> FlowName p <$> flowTypeName p)

    flowDecl (FlowName p name) =
      if Export p `elem` exports || exportDeps opts
      then showTypeAs (renderOptions opts) True name (flowType p) (flowTypeVars p)
      else showTypeAs (renderOptions opts) False name (flowType p) (flowTypeVars p)

writeModule :: ModuleOptions -> FilePath -> [Export] -> IO ()
writeModule opts path =
  TIO.writeFile path . generateModule opts

--------------------------------------------------------------------------------

-- | 'flowType' using 'Generic'
defaultFlowType :: (Generic a, GFlowTyped (Rep a)) => Options -> Proxy a -> FlowType
defaultFlowType opt p
  | unwrapUnaryRecords opt = error "aeson-flowtype does not yet support the unwrapUnaryRecords option."
  | otherwise = gflowType opt (fmap from p)

-- | 'flowTypeName' using 'Generic'
defaultFlowTypeName
  :: (Generic a, Rep a ~ D1 ('MetaData name mod pkg t) c, KnownSymbol name)
  => Proxy a
  -> Maybe Text
defaultFlowTypeName p
  = Just
  . cleanup
  . T.pack
  . symbolVal
  . pGetName
  . fmap from
  $ p
  where
    pGetName :: Proxy (D1 ('MetaData name mod pkg t) c x) -> Proxy name
    pGetName _ = Proxy

    cleanup = T.replace "'" "_" -- I think this is the only illegal token in JS
                                -- that's allowed in Haskell, other than type
                                -- operators... TODO, rename type operators


callType' :: (FlowCallable a) => Proxy a -> [FlowType] -> FlowType
callType' p args = case flowTypeName p of
  Just n -> FCallType (FlowName p n) args
  Nothing -> flowType p
  where
    vars = flowTypeVars p

callType :: forall a. FlowCallable a => Proxy a -> FlowType
callType p = callType' p
  (map (\(Flowable t) -> callType t)
  (reflTyParams @(TyParams a)))

class (ReflTyParams (TyParams a), Typeable a, FlowTyped a) => FlowCallable a
instance (ReflTyParams (TyParams a), Typeable a, FlowTyped a) => FlowCallable a

class FlowTyped a where
  flowType :: Proxy a -> FlowType
  flowTypeName :: Proxy a -> Maybe Text

  flowTypeVars :: Proxy a -> [Flowable]
  flowTypeVars _ = []

  flowOptions :: Proxy a -> Options
  flowOptions _ = A.defaultOptions

  isPrim :: Proxy a -> Bool
  isPrim _ = False

  default flowType :: (Generic a, GFlowTyped (Rep a)) => Proxy a -> FlowType
  flowType p = defaultFlowType (flowOptions p) p

  default flowTypeName
    :: (Generic a, Rep a ~ D1 ('MetaData name mod pkg t) c, KnownSymbol name)
    => Proxy a
    -> Maybe Text
  flowTypeName = defaultFlowTypeName

data Param (p :: Nat) = Param

--------------------------------------------------------------------------------

type family NumTyParams_ (k :: t) (acc :: Nat) :: Nat where
  NumTyParams_ (f x) acc = NumTyParams_ f (1 + acc)
  NumTyParams_ _t acc = acc
type NumTyParams t = NumTyParams_ t 0

type family TyParams_ (t :: k) (xs :: [Type]):: [Type] where
  TyParams_ (f x) xs = TyParams_ f (x ': xs)
  TyParams_ _constr xs = xs
type TyParams t = TyParams_ t '[]

class ReflTyParams (xs :: [Type]) where
  reflTyParams :: [Flowable]

instance ReflTyParams '[] where
  reflTyParams = []

instance (FlowCallable x, ReflTyParams xs) => ReflTyParams (x ': xs) where
  reflTyParams = (Flowable (Proxy :: Proxy x)) : reflTyParams @xs

type family FlowDeconstructField (k :: t) :: (Symbol, Type)
type instance FlowDeconstructField '(a, b) = '(a, b)

-- | Useful for declaring flowtypes from type-level key/value sets, like
--
-- @
-- FlowTyFields :: FlowTyFields Person '['("name", String), '("email", String)]
-- @
data FlowTyFields :: Type -> [k] -> Type where
  FlowTyFields :: FlowTyFields k fs

class ReifyFlowTyFields a where
  reifyFlowTyFields :: Proxy a -> HashMap Text FlowType -> HashMap Text FlowType

instance ReifyFlowTyFields '[] where
  reifyFlowTyFields _ = id

instance ( FlowDeconstructField x ~ '(k, v)
         , KnownSymbol k
         , FlowTyped v
         , ReifyFlowTyFields xs
         ) =>
         ReifyFlowTyFields (x:xs) where
  reifyFlowTyFields _ acc =
    reifyFlowTyFields (Proxy :: Proxy xs) $!
    H.insert
    (T.pack (symbolVal (Proxy :: Proxy k)))
    (flowType (Proxy :: Proxy v))
    acc

instance (FlowTyped a, ReifyFlowTyFields fs) => FlowTyped (FlowTyFields a fs) where
  flowType _ = FExactObject (reifyFlowTyFields (Proxy :: Proxy fs) H.empty)
  flowTypeName _ = flowTypeName (Proxy :: Proxy a)

--------------------------------------------------------------------------------

class GFlowTyped g where
  gflowType :: Options -> Proxy (g x) -> FlowType

class GFlowVal g where
  gflowVal :: Options -> Proxy (g x) -> GFlowTypeI

instance (KnownSymbol name, GFlowVal c) =>
         GFlowTyped (D1 ('MetaData name mod pkg t) c) where
  gflowType opt _ = runFlowI (postprocess (gflowVal opt (Proxy :: Proxy (c x))))
    where
      postprocess :: GFlowTypeI -> GFlowTypeI
      postprocess i
#if MIN_VERSION_aeson(1,2,0)
        | not (tagSingleConstructors opt), Just o <- removeSingleConstructorTag i =
          o
#endif
        | allNullaryToStringTag opt, Just r <- go [] i, not (null r) =
          foldr1
          (\a b -> FC (NoInfo (Alt a b)))
          (map (FC . NoInfo . Tag) r)
        | otherwise = i
        where
#if MIN_VERSION_aeson(1,2,0)
          removeSingleConstructorTag :: GFlowTypeI -> Maybe GFlowTypeI
          removeSingleConstructorTag (FC (Info (ExactObject hm))) =
            case sumEncoding opt of
              TaggedObject tfn _ ->
                Just (FC (Info (ExactObject (H.delete (T.pack tfn) hm))))
              _ ->
                Nothing
          removeSingleConstructorTag _ =
            Nothing
#endif

          -- no-field constructors have a "contents" field of Prim Void
          isNullary :: GFlowTypeI -> Bool
          isNullary (FC (Info (Prim a))) = case a of
            Bottom    -> True
            Null      -> True
            Undefined -> True
            _         -> False
          isNullary _ = False

          -- try to detect if the type is a bunch of single-constructor
          -- alternatives
          --
          -- XXX: this should preserve the order in which they are declared
          -- ... but does it?
          go :: [Text] -> GFlowTypeI -> Maybe [Text]
          go alts (FC (Constr name h _)) = (name:alts) <$ guard (isNullary h)
          go alts (FC (NoInfo (Alt a b))) =
            case (a, b) of
              (FC (Constr nameA ha _), FC (Constr nameB hb _)) ->
                (nameA:nameB:alts) <$
                guard (isNullary ha && isNullary hb)
              (FC (Constr nameA ha _), b') -> do
                guard (isNullary ha)
                (nameA:) <$> go alts b'
              (a', FC (Constr nameB hb _)) -> do
                guard (isNullary hb)
                (nameB:) <$> go alts a'
              _ -> do
                as <- go alts a
                bs <- go [] b
                return (as ++ bs)
          go _ _ =
            Nothing

      runFlowI :: GFlowTypeI -> FlowType
      runFlowI = cata $ \(Compose i) -> case i of
        Constr _name _t a -> Fix a
        NoInfo a          -> Fix a

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

noInfo :: f (Fix (Compose GFlowInfo f)) -> Fix (Compose GFlowInfo f)
noInfo = Fix . Compose . NoInfo

infoConstr :: Text -> GFlowTypeI -> f (Fix (Compose GFlowInfo f)) -> Fix (Compose GFlowInfo f)
infoConstr tag nxt = Fix . Compose . Constr tag nxt

discardInfo :: GFlowInfo a -> a
discardInfo (NoInfo a)     = a
discardInfo (Constr _ _ a) = a

pattern Info :: a -> GFlowInfo a
pattern Info a <- (discardInfo -> a)
  where Info = NoInfo

pattern FC :: f (g (Fix (Compose f g))) -> Fix (Compose f g)
pattern FC a = Fix (Compose a)

instance (KnownSymbol conName, GFlowRecord r) =>
         GFlowVal (C1 ('MetaCons conName fx 'True) r) where
  gflowVal opt p = noInfo $ case sumEncoding opt of
    TaggedObject tfn _ -> ExactObject $!
      H.insert (T.pack tfn) (noInfo (Tag tagName))
      next
    UntaggedValue -> Object next
    ObjectWithSingleField -> ExactObject (H.fromList [(tagName, noInfo (Object next))])
    TwoElemArray -> Tuple (V.fromList [noInfo (Tag tagName), noInfo (Object next)])
    where
      omitNothings =
        if omitNothingFields opt
        then H.map $ \t -> case t of
          FNullable a -> FOmitable a
          _          -> t
        else traceShow opt id

      next =
        H.map
        (cata noInfo)
        (omitNothings (gflowRecordFields opt (fmap unM1 p)))

      tagName = gconstrName opt p

instance (KnownSymbol conName, GFlowVal r) =>
         GFlowVal (C1 ('MetaCons conName fx 'False) r) where
  gflowVal opt p = infoConstr tagName next $ case sumEncoding opt of
    TaggedObject tfn cfn -> ExactObject (H.fromList
      [ (T.pack tfn, noInfo (Tag tagName))
      , (T.pack cfn, next)
      ])
    UntaggedValue -> discardInfo n
    ObjectWithSingleField -> ExactObject (H.fromList [(tagName, next)])
    TwoElemArray -> Tuple (V.fromList [noInfo (Tag tagName), next])
    where
      next@(Fix (Compose n)) = gflowVal opt (fmap unM1 p)
      tagName = gconstrName opt p

instance GFlowVal f => GFlowVal (M1 i ('MetaSel mj du ds dl) f) where
  gflowVal opt p = gflowVal opt (fmap unM1 p)

instance FlowCallable r => GFlowVal (Rec0 r) where
  gflowVal _opt (p :: r' x) =
    cata noInfo (callType (fmap unK1 p))

instance (GFlowVal a, GFlowVal b) => GFlowVal (a :+: b) where
  gflowVal opt _ = noInfo
    (Alt
     (gflowVal opt (Proxy :: Proxy (a x)))
     (gflowVal opt (Proxy :: Proxy (b x))))

instance (GFlowVal a, GFlowVal b) => GFlowVal (a :*: b) where
  gflowVal opt _ = noInfo $
    case (fA, fB) of
      (Tuple tfA, Tuple tfB) -> Tuple (tfA V.++ tfB)
      (Tuple tfA, _)         -> Tuple (V.snoc tfA b)
      (_        , Tuple tfB) -> Tuple (V.cons a tfB)
      _                      -> Tuple (V.fromList [a, b])
    where
      a@(Fix (Compose (Info fA))) = gflowVal opt (Proxy :: Proxy (a x))
      b@(Fix (Compose (Info fB))) = gflowVal opt (Proxy :: Proxy (b x))

instance GFlowVal U1 where
  gflowVal _ _ = noInfo (Prim Undefined)

class GFlowRecord a where
  gflowRecordFields :: Options -> Proxy (a x) -> HashMap Text FlowType

instance (KnownSymbol fieldName, GFlowVal ty) =>
         GFlowRecord (S1 ('MetaSel ('Just fieldName) su ss ds) ty) where
  gflowRecordFields opt p =
    H.singleton
    (gfieldName opt p)
    (cata
     (Fix . discardInfo . getCompose)
     (gflowVal opt (Proxy :: Proxy (ty x))))

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

instance (FlowCallable a) => FlowTyped [a] where
  flowType _ = FArray (callType (Proxy :: Proxy a))
  isPrim _ = True
  flowTypeName _ = Nothing

instance (FlowCallable a) => FlowTyped (Vector a) where
  flowType _ = FArray (callType (Proxy :: Proxy a))
  isPrim _ = True
  flowTypeName _ = Nothing

instance (FlowCallable a) => FlowTyped (VU.Vector a) where
  flowType _ = FArray (callType (Proxy :: Proxy a))
  isPrim _ = True
  flowTypeName _ = Nothing

instance (FlowCallable a) => FlowTyped (VS.Vector a) where
  flowType _ = FArray (callType (Proxy :: Proxy a))
  isPrim _ = True
  flowTypeName _ = Nothing

instance ( FlowCallable a
         , FlowCallable b) => FlowTyped (a, b) where
  flowTypeName _ = Nothing
  flowType _ =
    FTuple (V.fromList [aFt, bFt])
    where
      aFt = callType (Proxy :: Proxy a)
      bFt = callType (Proxy :: Proxy b)

instance (FlowCallable a) => FlowTyped (Maybe a) where
  flowType _ = FNullable (callType (Proxy :: Proxy a))
  isPrim _ = True
  flowTypeName _ = Nothing

instance ( FlowCallable a
         , FlowCallable b) =>
         FlowTyped (Either a b) where
  flowTypeName _ = Nothing
  flowType _ = FAlt
    (FExactObject (H.fromList [("Left", aFt)]))
    (FExactObject (H.fromList [("Right", bFt)]))
    where
      aFt = callType (Proxy :: Proxy a)
      bFt = callType (Proxy :: Proxy b)

instance ( FlowCallable a
         , FlowCallable b
         , FlowCallable c) =>
         FlowTyped (a, b, c) where
  flowTypeName _ = Nothing
  flowType _ = FTuple (V.fromList [aFt, bFt, cFt])
    where
      aFt = callType (Proxy :: Proxy a)
      bFt = callType (Proxy :: Proxy b)
      cFt = callType (Proxy :: Proxy c)

instance ( FlowCallable a
         , FlowCallable b
         , FlowCallable c
         , FlowCallable d
         ) =>
         FlowTyped (a, b, c, d) where
  flowTypeName _ = Nothing
  flowType _ = FTuple (V.fromList [aFt, bFt, cFt, dFt])
    where
      aFt = callType (Proxy :: Proxy a)
      bFt = callType (Proxy :: Proxy b)
      cFt = callType (Proxy :: Proxy c)
      dFt = callType (Proxy :: Proxy d)

instance ( FlowCallable a
         , FlowCallable b
         , FlowCallable c
         , FlowCallable d
         , FlowCallable e
         ) =>
         FlowTyped (a, b, c, d, e) where
  flowTypeName _ = Nothing
  flowType _ = FTuple (V.fromList [aFt, bFt, cFt, dFt, eFt])
    where
      aFt = callType (Proxy :: Proxy a)
      bFt = callType (Proxy :: Proxy b)
      cFt = callType (Proxy :: Proxy c)
      dFt = callType (Proxy :: Proxy d)
      eFt = callType (Proxy :: Proxy e)

instance FlowTyped Text where
  isPrim  _ = True
  flowType _ = FPrimString
  flowTypeName _ = Nothing

instance FlowTyped TL.Text where
  isPrim  _ = True
  flowType _ = FPrimString
  flowTypeName _ = Nothing

instance {-# OVERLAPS #-} FlowTyped String where
  isPrim  _ = True
  flowType _ = FPrimString
  flowTypeName _ = Nothing

instance FlowTyped Void.Void where
  isPrim  _ = True
  flowType _ = FPrimBottom
  flowTypeName _ = Nothing

instance FlowTyped Char where
  isPrim  _ = True
  flowType _ = FPrimString
  flowTypeName _ = Nothing

instance FlowTyped Bool where
  isPrim  _ = True
  flowType _ = FPrimBoolean
  flowTypeName _ = Nothing

instance FlowTyped A.Value where
  isPrim  _ = True
  flowType _ = FPrimMixed
  flowTypeName _ = Nothing

instance FlowTyped UTCTime where
  isPrim  _ = False
  flowType _ = FPrimString
  flowTypeName _ = Nothing

instance Typeable a => FlowTyped (Fixed a) where
  isPrim  _ = False
  flowType _ = FPrimNumber
  flowTypeName _ = Nothing

instance ( FlowCallable k
         , FlowCallable a
         , A.ToJSONKey k
         ) => FlowTyped (HashMap k a) where
  -- XXX this is getting quite incoherent, what makes something "Prim" or not...
  isPrim _ = True

  flowType _ =
    case A.toJSONKey :: A.ToJSONKeyFunction k of
      A.ToJSONKeyText{} ->
        FObjectMap "key" FPrimString (callType (Proxy :: Proxy a))

      A.ToJSONKeyValue{} ->
        FArray (FTuple (V.fromListN 2
                        [ callType (Proxy :: Proxy k)
                        , callType (Proxy :: Proxy a)
                        ]))

  flowTypeName _ =
    Nothing

instance (FlowCallable a) => FlowTyped (Set.Set a) where
  isPrim _ = False
  flowType _ = FArray (callType (Proxy :: Proxy a))
  flowTypeName _ = Nothing

instance FlowTyped IntSet.IntSet where
  isPrim _ = False
  flowType _ = FArray FPrimNumber -- (Fix (Prim Number))
  flowTypeName _ = Nothing

instance (FlowCallable a) => FlowTyped (I.IntMap a) where
  isPrim _ = False
  flowType _ = Fix . Array . Fix . Tuple . V.fromListN 2 $
    [ FPrimNumber
    , callType (Proxy :: Proxy a)
    ]
  flowTypeName _ = Nothing

instance (FlowCallable a) => FlowTyped (HashSet.HashSet a) where
  isPrim _ = False
  flowType _ = FArray (callType (Proxy :: Proxy a))
  flowTypeName _ = Nothing

-- | This instance is defined recursively. You'll probably need to use
-- 'dependencies' to extract a usable definition
instance (FlowCallable a) => FlowTyped (Tree.Tree a) where
  isPrim _ = False
  flowType _ = FTuple
    (V.fromList
     [ FGenericParam 0
     , FArray (callType' (Proxy :: Proxy (Tree.Tree a)) [FGenericParam 0])
     ])
  flowTypeName _ = Just "Tree"
  flowTypeVars _ = [Flowable (Proxy :: Proxy a)]

instance FlowTyped () where
  isPrim _ = False
  flowType _ = FTuple V.empty
  flowTypeName _ = Nothing

-- monomorphic numeric instances
$(concat <$> mapM
  (\ty ->
     [d|
      instance FlowTyped $ty where
        isPrim  _ = False
        flowType _ = FPrimNumber
        flowTypeName _ = Nothing |])
  [ [t|Int|], [t|Int8|], [t|Int16|], [t|Int32|], [t|Int64|]
  , [t|Word|], [t|Word8|], [t|Word16|], [t|Word32|], [t|Word64|]
  , [t|Float|], [t|Double|], [t|Scientific|]
  ])

deriveEq1 ''FlowTypeF
