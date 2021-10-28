{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE DefaultSignatures         #-}
{-# LANGUAGE DeriveAnyClass            #-}
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
    FlowTyped(..)
  , callType
  , FlowTypeF
  , FlowType
  -- , Fix (..)
  , pattern FObject
  , pattern FExactObject
  , pattern FObjectMap
  , pattern FArray
  , pattern FTuple
  , pattern FLabelledTuple
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
    -- ** Wholesale ES6/flow/typescript modules
  , Export
  , export
  , RenderMode(..)
  , RenderOptions(..)
  , ModuleOptions(..)
  , typeScriptModuleOptions
  , flowModuleOptions
  , generateModule
  , writeModule
  , showTypeAs
  , exportTypeAs
    -- ** Convenience for generating flowtypes from other types
  , FlowTyFields(..)
  , FlowDeconstructField
    -- ** TS specific
  , showTypeScriptType
    -- ** Flow specific
  , showFlowType
    -- * Dependencies
  , exportsDependencies
  , dependencies
    -- * Utility
  , FlowName(..)
  , Flowable(..)
  , defaultFlowTypeName
  , defaultFlowType
  ) where
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import qualified Data.Aeson                    as A
import           Data.Aeson.Types               ( Options(..)
                                                , SumEncoding(..)
                                                )
import           Data.Eq.Deriving               ( deriveEq1 )
import           Data.Fix                       ( Fix(..) )
import           Data.Fixed                     ( Fixed )
import           Data.Functor.Classes
import           Data.HashMap.Strict            ( HashMap )
import qualified Data.HashMap.Strict           as H
import qualified Data.HashSet                  as HashSet
import           Data.Int
import qualified Data.IntMap.Strict            as I
import qualified Data.IntSet                   as IntSet
import qualified Data.Map.Strict               as M
import           Data.Maybe
import qualified Data.Monoid                   as Monoid
import           Data.Proxy
import           Data.Reflection
import           Data.Scientific                ( Scientific )
import qualified Data.Set                      as Set
import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import qualified Data.Text.IO                  as TIO
import qualified Data.Text.Lazy                as TL
import           Data.Time                      ( UTCTime )
import qualified Data.Tree                     as Tree
import           Data.Typeable
import           Data.Vector                    ( Vector )
import qualified Data.Vector                   as V
import qualified Data.Vector.Storable          as VS
import qualified Data.Vector.Unboxed           as VU
import qualified Data.Void                     as Void
import           Data.Word
import           GHC.Generics                   ( D1
                                                , Generic
                                                , Meta(..)
                                                , Rep
                                                , from
                                                )
import           GHC.TypeLits
import qualified Generics.SOP                  as SOP
import qualified Generics.SOP.GGP              as SOP
import qualified Text.PrettyPrint.Leijen       as PP

-- | The main AST for flowtypes.
data FlowTypeF a
  = Object !(HashMap Text a)
  | ExactObject !(HashMap Text a)
  | ObjectMap !Text a a
  | Array a
  | Tuple !(Vector a)
  | LabelledTuple !(Vector (Maybe Text, a))
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
  | TypeDoc !(Vector Text) a
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
  FlowName ::(FlowTyped a) => Proxy a -> Text -> FlowName

data Flowable where
  Flowable ::(FlowTyped a) => Proxy a -> Flowable

data Showy f a = forall s . Reifies s (Int -> a -> ShowS) => Showy
                                                               (f (Inj s a))
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
  }
  deriving (Eq, Show)

instance Show FlowName where
  show (FlowName _ t) = show t

instance Eq FlowName where
  FlowName _t0 n0 == FlowName _t1 n1 = n0 == n1
    -- case eqT :: Maybe (t0 :~: t1) of
    --   Just Refl -> (t0, n0) == (t1, n1)
    --   Nothing -> False

instance Ord FlowName where
  FlowName _t0 n0 `compare` FlowName _t1 n1 = n0 `compare` n1
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

pattern FLabelledTuple :: Vector (Maybe Text, FlowType) -> FlowType
pattern FLabelledTuple a = Fix (LabelledTuple a)

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

pattern FTypeDoc :: Vector Text -> FlowType -> FlowType
pattern FTypeDoc f xs = Fix (TypeDoc f xs)

--------------------------------------------------------------------------------

instance Show1 FlowTypeF where
  liftShowsPrec sp sl i a =
    liftShowsPrec sp sl i (reify sp (\p -> Showy (fmap (inj p) a)))

type FlowType = Fix FlowTypeF

text :: Text -> PP.Doc
text = PP.text . T.unpack

squotes :: Text -> PP.Doc
squotes = PP.squotes . text . T.replace "'" "\\'"

type Poly = ReaderT RenderOptions (Reader [Flowable])

ppAlts :: [FlowType] -> FlowType -> Poly PP.Doc
ppAlts alts (Fix f) = case f of
  Alt a b -> ppAlts (a : alts) b
  x -> PP.align . sep <$> mapM pp (reverse (Fix x : alts))
 where
  sep [x] = x
  sep (x : xs) = x PP.<+> PP.string "|" PP.<$> sep xs
  sep _ = PP.empty

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
  A.Array a -> PP.list (map ppJson (V.toList a))
  A.String t -> squotes t
  A.Number n -> PP.string (show n)
  A.Bool t -> if t then PP.string "true" else PP.string "false"
  A.Null -> PP.string "null"
  A.Object obj -> braceBarList
    (map
      (\(name, fty) ->
        PP.space
          PP.<> text name
          PP.<+> PP.colon
          PP.<+> ppJson fty
          PP.<> PP.space
      )
      (H.toList obj)
    )

mayWrap :: FlowType -> PP.Doc -> PP.Doc
mayWrap (Fix f) x = case f of
  Nullable _ -> PP.parens x
  Omitable _ -> PP.parens x
  Alt _ _ -> PP.parens x
  Array _ -> PP.parens x
  _ -> x

ppObject :: HashMap Text FlowType -> Poly [PP.Doc]
ppObject = mapM ppField . H.toList
 where
  ppField (name, fty) = do
    case fty of
      Fix (Omitable fty') ->
        -- key?: type
        (\fty'' -> text name PP.<> PP.text "?" PP.<> PP.colon PP.<+> fty'')
          <$> pp fty'

      fty' ->
        -- key: type
        (\fty'' -> text name PP.<> PP.colon PP.<+> fty'') <$> pp fty'

polyVarNames :: [Text]
polyVarNames =
  map T.singleton ['A' .. 'Z']
    ++ zipWith (\i t -> t `T.append` T.pack (show i)) [0 :: Int ..] polyVarNames

pp :: FlowType -> Poly PP.Doc
pp (Fix ft) = case ft of
  ObjectMap keyName keyType a -> do
    keyTy <- pp keyType
    r <- pp a
    pure
      (braceList
        [ PP.brackets (text keyName PP.<> PP.text ":" PP.<+> keyTy)
          PP.<> PP.colon
          PP.<+> r
        ]
      )

  Object hm -> braceList <$> ppObject hm

  ExactObject hm -> do
    mode <- asks renderMode
    case mode of
      RenderFlow -> braceBarList <$> ppObject hm
      RenderTypeScript -> braceList <$> ppObject hm

  -- x[]
  Array a -> (\r -> mayWrap a r PP.<> PP.string "[]") <$> pp a

  -- [x, y, z]
  Tuple t -> PP.list <$> mapM pp (V.toList t)

  -- [l1: x, y, l2: z]
  LabelledTuple t -> PP.list <$> mapM
    (\(mlbl, ty) -> case mlbl of
      Just lbl -> ((text lbl PP.<> PP.string ":") PP.<+>) <$> pp ty
      Nothing -> pp ty
    )
    (V.toList t)

  Alt a b -> ppAlts [a] b

  Prim pt -> do
    mode <- asks renderMode
    return $ case pt of
      Boolean -> PP.text "boolean"
      Number -> PP.text "number"
      String -> PP.text "string"
      Null -> PP.text "null"
      Undefined -> PP.text "undefined"
      Any -> PP.text "any"
      Mixed -> case mode of
        RenderFlow -> PP.text "mixed"
        RenderTypeScript -> PP.text "unknown"
      Bottom -> case mode of
        RenderFlow -> PP.text "empty"
        RenderTypeScript -> PP.text "never"

  Nullable a ->
    -- n.b. there is no 'undefined' in json. void is undefined | null in both ts
    -- and flow (and ?x syntax for void|x)
    (\a' -> PP.text "null" PP.<+> PP.string "|" PP.<+> a') <$> pp a

  Omitable a -> pp (FNullable a)

  Literal a -> return (ppJson a)

  Tag t -> return (squotes t)

  GenericParam ix -> return (text (polyVarNames !! ix))

  CallType (FlowName _ t) [] -> return (text t)

  CallType (FlowName _ t) args -> do
    vs <- mapM pp args
    return (text t PP.<> PP.angles (PP.hsep (PP.punctuate PP.comma vs)))

  TypeDoc _doc t -> pp t

  _ -> return (PP.string (show ft))

-- | Pretty-print a flowtype in flowtype syntax
renderTypeWithOptions :: RenderOptions -> FlowType -> [Flowable] -> PP.Doc
renderTypeWithOptions opts ft params =
  (pp ft `runReaderT` opts) `runReader` params

-- | Pretty-print a flowtype in flowtype syntax
showFlowType :: FlowType -> [Flowable] -> Text
showFlowType ft params = T.pack . show $ renderTypeWithOptions
  RenderOptions { renderMode = RenderFlow }
  ft
  params

-- | Pretty-print a flowtype in flowtype syntax
showTypeScriptType :: FlowType -> [Flowable] -> Text
showTypeScriptType ft params = T.pack . show $ renderTypeWithOptions
  RenderOptions { renderMode = RenderTypeScript }
  ft
  params

--------------------------------------------------------------------------------
-- Module exporting

-- | Generate a @ export type @ declaration.
exportTypeAs :: RenderOptions -> Text -> FlowType -> [Flowable] -> Text
exportTypeAs opts = showTypeAs opts True

-- | Generate a @ type @ declaration, possibly an export.
showTypeAs :: RenderOptions -> Bool -> Text -> FlowType -> [Flowable] -> Text
showTypeAs opts isExport name ft params =
  T.pack
    . render
    $ PP.string (if isExport then "export type " else "type ")
    PP.<> text name
    PP.<> renderedParams
    PP.<+> text "="
    PP.<+> renderedTypeDecl
    PP.<> text ";"
    PP.<> PP.linebreak
 where
  renderedTypeDecl = renderTypeWithOptions opts ft params
  renderedParams
    | null params = mempty
    | otherwise = PP.angles
      (PP.hsep
        (PP.punctuate PP.comma (map text (take (length params) polyVarNames)))
      )

  render = ($ []) . PP.displayS . PP.renderPretty 1.0 80

-- | Compute all the dependencies of a 'FlowTyped' thing, including itself.
dependencies :: (FlowTyped a) => Proxy a -> Set.Set FlowName
dependencies p0 =
  (case flowTypeName p0 of
      Just t -> Set.insert (FlowName p0 t)
      Nothing -> id
    )
    (M.foldl' Set.union Set.empty (transitiveDeps (Flowable p0) M.empty))
 where
  flowNameToFlowable (FlowName fn _) = Flowable fn

  immediateDeps :: FlowType -> Set.Set FlowName
  immediateDeps (FCallType n tys) =
    Set.insert n (Set.unions (map immediateDeps tys))
  immediateDeps (Fix p) = foldMap immediateDeps p

  transitiveDeps
    :: Flowable
    -> M.Map Flowable (Set.Set FlowName)
    -> M.Map Flowable (Set.Set FlowName)
  transitiveDeps fpf@(Flowable p) acc
    | fpf `M.notMember` acc
    = let imms = immediateDeps (flowType p)
          withThis = M.insert fpf imms acc
      in  Set.foldr' (transitiveDeps . flowNameToFlowable) withThis imms
    | otherwise
    = acc

data ModuleOptions = ModuleOptions
  { -- | You might want to change this to include e.g. flow-runtime
    pragmas :: [Text]
  , header :: [Text]
  , exportDeps :: Bool
  , computeDeps :: Bool
  , renderOptions :: RenderOptions
  }
  deriving (Eq, Show)

flowModuleOptions :: ModuleOptions
flowModuleOptions = ModuleOptions
  { pragmas = ["// @flow"]
  , header = ["This module has been generated by aeson-flowtyped."]
  , exportDeps = True
  , computeDeps = True
  , renderOptions = RenderOptions { renderMode = RenderFlow }
  }

typeScriptModuleOptions :: ModuleOptions
typeScriptModuleOptions = ModuleOptions
  { pragmas = []
  , header = ["This module has been generated by aeson-flowtyped."]
  , exportDeps = True
  , computeDeps = True
  , renderOptions = RenderOptions { renderMode = RenderTypeScript }
  }

data Export where
  Export ::FlowTyped a => Proxy a -> Export

export :: forall a . FlowTyped a => Export
export = Export (Proxy :: Proxy a)

instance Eq Export where
  Export p0 == Export p1 =
    flowTypeName p0 == flowTypeName p1 || typeRep p0 == typeRep p1

exportsDependencies :: [Export] -> Set.Set FlowName
exportsDependencies = foldMap $ \e -> case e of
  Export a -> dependencies a

generateModule :: ModuleOptions -> [Export] -> Text
generateModule opts exports =
  T.unlines
    $ (\m ->
        (pragmas opts ++ map ("// " `T.append`) (header opts)) ++ (T.empty : m)
      )
    . map flowDecl
    . flowNames
    $ exports
 where
  flowNames = if computeDeps opts
    then Set.toList . exportsDependencies
    else catMaybes . map
      (\ex -> case ex of
        Export p -> FlowName p <$> flowTypeName p
      )

  flowDecl (FlowName p name) = if Export p `elem` exports || exportDeps opts
    then showTypeAs (renderOptions opts) True name (flowType p) (flowTypeVars p)
    else showTypeAs (renderOptions opts)
                    False
                    name
                    (flowType p)
                    (flowTypeVars p)

writeModule :: ModuleOptions -> FilePath -> [Export] -> IO ()
writeModule opts path = TIO.writeFile path . generateModule opts

--------------------------------------------------------------------------------

type family FlowDeconstructField (k :: t) :: (Symbol, *)
type instance FlowDeconstructField '(a, b) = '(a, b)

-- | Useful for declaring flowtypes from type-level key/value sets, like
--
-- @
-- FlowTyFields :: FlowTyFields Person '['("name", String), '("email", String)]
-- @
data FlowTyFields :: * -> [k] -> * where
  FlowTyFields ::FlowTyFields k fs

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
    reifyFlowTyFields (Proxy :: Proxy xs)
      $! H.insert (T.pack (symbolVal (Proxy :: Proxy k)))
                  (flowType (Proxy :: Proxy v))
                  acc

instance (FlowTyped a, ReifyFlowTyFields (fs :: [k]), Typeable fs, Typeable k) => FlowTyped (FlowTyFields a fs) where
  flowType _ = FExactObject (reifyFlowTyFields (Proxy :: Proxy fs) H.empty)
  flowTypeName _ = flowTypeName (Proxy :: Proxy a)

--------------------------------------------------------------------------------

callType' :: (FlowTyped a) => Proxy a -> [FlowType] -> FlowType
callType' p args = case flowTypeName p of
  Just n -> FCallType (FlowName p n) args
  Nothing -> flowType p

callType :: forall a . FlowTyped a => Proxy a -> FlowType
callType p = callType' p (map (\(Flowable t) -> callType t) (flowTypeVars p))

class Typeable a => FlowTyped a where
  flowType :: Proxy a -> FlowType
  flowTypeName :: Proxy a -> Maybe Text

  flowTypeVars :: Proxy a -> [Flowable]
  flowTypeVars _ = []

  flowOptions :: Proxy a -> Options
  flowOptions _ = A.defaultOptions

  isPrim :: Proxy a -> Bool
  isPrim _ = False

  default flowType
    :: (SOP.GDatatypeInfo a, SOP.All2 FlowTyped (SOP.GCode a))
    => Proxy a
    -> FlowType
  flowType p = flowTypeFromSOP (flowOptions p) (SOP.gdatatypeInfo p)

  default flowTypeName
    :: (Generic a, Rep a ~ D1 ('MetaData name mod pkg t) c, KnownSymbol name)
    => Proxy a
    -> Maybe Text
  flowTypeName = defaultFlowTypeName

-- | 'flowType' using 'SOP.HasDatatypeInfo'
defaultFlowType
  :: (SOP.HasDatatypeInfo a, SOP.All2 FlowTyped (SOP.Code a))
  => Options
  -> Proxy a
  -> FlowType
defaultFlowType opts p = flowTypeFromSOP opts (SOP.datatypeInfo p)

flowTypeFromSOP
  :: SOP.All2 FlowTyped ty => Options -> SOP.DatatypeInfo ty -> FlowType
flowTypeFromSOP opts di = case comments of
  [] -> ft
  _ -> FTypeDoc (V.fromList comments) ft
 where
  (ft, comments) =
    (case di of
        SOP.ADT moduleName typeName constrInfos _strictness -> do
          modify' (moduleComment moduleName :)
          modify' (typeComment typeName :)
          pure . foldr1 FAlt $! case constrsKind constrInfos 0 0 0 True of
            SumRecords -> sumEncode constrInfos
            SumConstructors -> sumEncode constrInfos
            SumNullaryConstructors -> sumNullaryEncode constrInfos
            SingleRecord -> singleEncode constrInfos
            SingleConstructor -> singleEncode constrInfos
            SingleNullaryConstructor -> [FTuple V.empty]
            Unsupported ->
              error $ "aeson-flowtyped: Unsupported type " ++ show typeName

        SOP.Newtype moduleName typeName constrInfo -> do
          modify' (moduleComment moduleName :)
          modify' (typeComment typeName :)
          case constrInfo of

            (SOP.Constructor constrName :: SOP.ConstructorInfo '[x]) -> do
              modify' (constrComment constrName :)
              pure (callType (Proxy :: Proxy x))

            SOP.Record constrName ((SOP.FieldInfo _fname :: SOP.FieldInfo x) SOP.:* SOP.Nil)
              -> do
                modify' (constrComment constrName :)
                pure (callType (Proxy :: Proxy x))
      )
      `runState` []

  constrsKind
    :: SOP.NP SOP.ConstructorInfo ty
    -> Int -- ^ total number of record or plain constructors
    -> Int -- ^ number of record constructors
    -> Int -- ^ number of plain constructors
    -> Bool -- ^ whether every constructor is nullary
    -> ConstructorsKind
  constrsKind SOP.Nil !total !recs !plains !allNullary
    | recs == 1 && plains == 0 = SingleRecord
    | plains == 1 && recs == 0 = if allNullary
      then SingleNullaryConstructor
      else SingleConstructor
    | recs == total && plains == 0 = SumRecords
    | plains == total && recs == 0 = if allNullary
      then SumNullaryConstructors
      else SumConstructors
    | otherwise = Unsupported
  constrsKind (constr SOP.:* rest) total recs plains allNullary =
    case constr of
      (SOP.Constructor{} :: SOP.ConstructorInfo flds) -> constrsKind
        rest
        (total + 1)
        recs
        (plains + 1)
        (allNullary && isNullary @flds)

      (SOP.Record{} :: SOP.ConstructorInfo flds) -> constrsKind
        rest
        (total + 1)
        (recs + 1)
        plains
        (allNullary && isNullary @flds)

      _ -> Unsupported

  sumEncode, singleEncode, sumNullaryEncode
    :: SOP.All2 FlowTyped ty => SOP.NP SOP.ConstructorInfo ty -> [FlowType]
  sumEncode constrsNP = SOP.hcfoldMap
    (Proxy :: Proxy (SOP.All FlowTyped))
    (\case
      (SOP.Constructor constrName :: SOP.ConstructorInfo xs) ->
        let
          value =
            let tuple = V.fromList $! SOP.hcfoldMap
                  (Proxy :: Proxy FlowTyped)
                  (\(Proxy :: SOP.Proxy x) -> [callType (Proxy :: Proxy x)])
                  (SOP.hpure Proxy :: SOP.NP Proxy xs)
            in  case V.length tuple of
                  1 -> V.head tuple
                  _ -> FTuple tuple

          hasContents = Monoid.getAny $! SOP.hcfoldMap
            (Proxy :: Proxy SOP.Top)
            (\_ -> Monoid.Any True)
            (SOP.hpure Proxy :: SOP.NP Proxy xs)
        in
          case sumEncoding opts of
            TaggedObject (T.pack -> tagFld) contentsFld
              | hasContents
              -> [ FExactObject
                     (H.fromList
                       [ (tagFld, renderConstrTag constrName)
                       , (T.pack contentsFld, value)
                       ]
                     )
                 ]
              | otherwise
              -> [ FExactObject
                     (H.singleton tagFld (renderConstrTag constrName))
                 ]
            UntaggedValue -> [value]
            ObjectWithSingleField ->
              [ FExactObject
                  (H.fromList
                    [(T.pack (constructorTagModifier opts constrName), value)]
                  )
              ]
            TwoElemArray ->
              [FTuple (V.fromListN 2 [renderConstrTag constrName, value])]

      SOP.Record constrName flds ->
        let
          fldsList :: H.HashMap Text FlowType
          fldsList =
            H.fromList
              $! SOP.hcfoldMap
                   (Proxy :: Proxy FlowTyped)
                   (\(SOP.FieldInfo fname :: SOP.FieldInfo x) ->
                     [ ( T.pack (fieldLabelModifier opts fname)
                       , callType (Proxy :: Proxy x)
                       )
                     ]
                   )
                   flds
        in
          case sumEncoding opts of
              -- The contents field is not used here but the tag one is
            TaggedObject (T.pack -> tagFld) _contentsFld ->
              [ FExactObject
                  (H.insert tagFld (renderConstrTag constrName) fldsList)
              ]
            UntaggedValue -> [FExactObject fldsList]
            ObjectWithSingleField ->
              [ FExactObject
                  (H.singleton
                    (T.pack (constructorTagModifier opts constrName))
                    (FExactObject fldsList)
                  )
              ]
            TwoElemArray ->
              [ FTuple
                  (V.fromListN
                    2
                    [renderConstrTag constrName, FExactObject fldsList]
                  )
              ]
      SOP.Infix{} ->
        error "aeson-flowtyped: Unsupported use of infix constructor"
    )
    constrsNP

  singleEncode (constr SOP.:* SOP.Nil) = case constr of
    (SOP.Constructor _constrName :: SOP.ConstructorInfo xs) ->
      [ FTuple . V.fromList $! SOP.hcfoldMap
          (Proxy :: Proxy FlowTyped)
          (\(Proxy :: SOP.Proxy x) -> [callType (Proxy :: Proxy x)])
          (SOP.hpure Proxy :: SOP.NP Proxy xs)
      ]
    SOP.Record _constrName flds ->
      [ FExactObject
          $! H.fromList
          $! SOP.hcfoldMap
               (Proxy :: Proxy FlowTyped)
               (\(SOP.FieldInfo fname :: SOP.FieldInfo x) ->
                 [ ( T.pack (fieldLabelModifier opts fname)
                   , callType (Proxy :: Proxy x)
                   )
                 ]
               )
               flds
      ]
    SOP.Infix{} ->
      error "aeson-flowtyped: Unsupported use of infix constructor"
  singleEncode _ =
    error "aeson-flowtyped: Errorneous detection of single constructor"

  sumNullaryEncode constrsNP
    | allNullaryToStringTag opts
    = [ FLiteral (A.String (T.pack (constructorTagModifier opts tag)))
      | tag <- SOP.hcfoldMap (Proxy :: Proxy SOP.Top)
                             (\(SOP.Constructor constrName) -> [constrName])
                             constrsNP
      ]
    | otherwise
    = [ nullarySumObject (T.pack (constructorTagModifier opts tag))
      | tag <- SOP.hcfoldMap (Proxy :: Proxy SOP.Top)
                             (\(SOP.Constructor constrName) -> [constrName])
                             constrsNP
      ]

  nullarySumObject tagValue = case sumEncoding opts of
    TaggedObject (T.pack -> tagFld) _contentsFld ->
      FExactObject (H.singleton tagFld (FLiteral (A.String tagValue)))
    UntaggedValue -> FTuple V.empty
    ObjectWithSingleField ->
      FExactObject (H.singleton tagValue (FTuple V.empty))
    TwoElemArray ->
      FTuple (V.fromListN 2 [FLiteral (A.String tagValue), FTuple V.empty])

  renderConstrTag = FLiteral . A.String . T.pack . constructorTagModifier opts

  moduleComment s = T.concat ["Origin module: `", T.pack s, "`"]
  typeComment s = T.concat ["Origin type: ", T.pack s]
  constrComment s = T.concat ["Origin constructor: ", T.pack s]

  isNullary :: forall xs . SOP.SListI xs => Bool
  isNullary = SOP.lengthSList (Proxy :: Proxy xs) == 0


data ConstructorsKind
  = SumRecords
  | SumConstructors
  | SumNullaryConstructors
  | SingleRecord
  | SingleConstructor
  | SingleNullaryConstructor
  | Unsupported

-- | 'flowTypeName' using 'Generic'
defaultFlowTypeName
  :: (Generic a, Rep a ~ D1 ('MetaData name mod pkg t) c, KnownSymbol name)
  => Proxy a
  -> Maybe Text
defaultFlowTypeName p =
  Just . cleanup . T.pack . symbolVal . pGetName . fmap from $ p
 where
  pGetName :: Proxy (D1 ( 'MetaData name mod pkg t) c x) -> Proxy name
  pGetName _ = Proxy
  cleanup = T.replace "'" "_" -- I think this is the only illegal token in JS
                                -- that's allowed in Haskell, other than type
                                -- operators... TODO, rename type operators

--------------------------------------------------------------------------------
-- Instances

instance (FlowTyped a) => FlowTyped [a] where
  flowType _ = FArray (callType (Proxy :: Proxy a))
  isPrim _ = True
  flowTypeName _ = Nothing

instance (FlowTyped a) => FlowTyped (Vector a) where
  flowType _ = FArray (callType (Proxy :: Proxy a))
  isPrim _ = True
  flowTypeName _ = Nothing

instance (FlowTyped a) => FlowTyped (VU.Vector a) where
  flowType _ = FArray (callType (Proxy :: Proxy a))
  isPrim _ = True
  flowTypeName _ = Nothing

instance (FlowTyped a) => FlowTyped (VS.Vector a) where
  flowType _ = FArray (callType (Proxy :: Proxy a))
  isPrim _ = True
  flowTypeName _ = Nothing

instance ( FlowTyped a
         , FlowTyped b
         ) => FlowTyped (a, b) where
  flowTypeName _ = Nothing
  flowType _ = FTuple (V.fromList [aFt, bFt])
   where
    aFt = callType (Proxy :: Proxy a)
    bFt = callType (Proxy :: Proxy b)

instance (FlowTyped a) => FlowTyped (Maybe a) where
  flowType _ = FNullable (callType (Proxy :: Proxy a))
  isPrim _ = True
  flowTypeName _ = Nothing

instance ( FlowTyped a
         , FlowTyped b) =>
         FlowTyped (Either a b) where
  flowTypeName _ = Nothing
  flowType _ = FAlt (FExactObject (H.fromList [("Left", aFt)]))
                    (FExactObject (H.fromList [("Right", bFt)]))
   where
    aFt = callType (Proxy :: Proxy a)
    bFt = callType (Proxy :: Proxy b)

instance ( FlowTyped a
         , FlowTyped b
         , FlowTyped c) =>
         FlowTyped (a, b, c) where
  flowTypeName _ = Nothing
  flowType _ = FTuple (V.fromList [aFt, bFt, cFt])
   where
    aFt = callType (Proxy :: Proxy a)
    bFt = callType (Proxy :: Proxy b)
    cFt = callType (Proxy :: Proxy c)

instance ( FlowTyped a
         , FlowTyped b
         , FlowTyped c
         , FlowTyped d
         ) =>
         FlowTyped (a, b, c, d) where
  flowTypeName _ = Nothing
  flowType _ = FTuple (V.fromList [aFt, bFt, cFt, dFt])
   where
    aFt = callType (Proxy :: Proxy a)
    bFt = callType (Proxy :: Proxy b)
    cFt = callType (Proxy :: Proxy c)
    dFt = callType (Proxy :: Proxy d)

instance ( FlowTyped a
         , FlowTyped b
         , FlowTyped c
         , FlowTyped d
         , FlowTyped e
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
  isPrim _ = True
  flowType _ = FPrimString
  flowTypeName _ = Nothing

instance FlowTyped TL.Text where
  isPrim _ = True
  flowType _ = FPrimString
  flowTypeName _ = Nothing

instance {-# OVERLAPS #-} FlowTyped String where
  isPrim _ = True
  flowType _ = FPrimString
  flowTypeName _ = Nothing

instance FlowTyped Void.Void where
  isPrim _ = True
  flowType _ = FPrimBottom
  flowTypeName _ = Nothing

instance FlowTyped Char where
  isPrim _ = True
  flowType _ = FPrimString
  flowTypeName _ = Nothing

instance FlowTyped Bool where
  isPrim _ = True
  flowType _ = FPrimBoolean
  flowTypeName _ = Nothing

instance FlowTyped A.Value where
  isPrim _ = True
  flowType _ = FPrimMixed
  flowTypeName _ = Nothing

instance FlowTyped UTCTime where
  isPrim _ = False
  flowType _ = FPrimString
  flowTypeName _ = Nothing

instance (Typeable (a :: k), Typeable k) => FlowTyped (Fixed a) where
  isPrim _ = False
  flowType _ = FPrimNumber
  flowTypeName _ = Nothing

instance ( FlowTyped k
         , FlowTyped a
         , A.ToJSONKey k
         ) => FlowTyped (HashMap k a) where
  -- XXX this is getting quite incoherent, what makes something "Prim" or not...
  isPrim _ = True

  flowType _ = case A.toJSONKey :: A.ToJSONKeyFunction k of
    A.ToJSONKeyText{} ->
      FObjectMap "key" FPrimString (callType (Proxy :: Proxy a))

    A.ToJSONKeyValue{} -> FArray
      (FTuple
        (V.fromListN
          2
          [callType (Proxy :: Proxy k), callType (Proxy :: Proxy a)]
        )
      )

  flowTypeName _ = Nothing

instance (FlowTyped a) => FlowTyped (Set.Set a) where
  isPrim _ = False
  flowType _ = FArray (callType (Proxy :: Proxy a))
  flowTypeName _ = Nothing

instance FlowTyped IntSet.IntSet where
  isPrim _ = False
  flowType _ = FArray FPrimNumber -- (Fix (Prim Number))
  flowTypeName _ = Nothing

instance (FlowTyped a) => FlowTyped (I.IntMap a) where
  isPrim _ = False
  flowType _ =
    Fix
      . Array
      . Fix
      . Tuple
      . V.fromListN 2
      $ [FPrimNumber, callType (Proxy :: Proxy a)]
  flowTypeName _ = Nothing

instance (FlowTyped a) => FlowTyped (HashSet.HashSet a) where
  isPrim _ = False
  flowType _ = FArray (callType (Proxy :: Proxy a))
  flowTypeName _ = Nothing

-- | This instance is defined recursively. You'll probably need to use
-- 'dependencies' to extract a usable definition
instance (FlowTyped a) => FlowTyped (Tree.Tree a) where
  isPrim _ = False
  flowType _ = FTuple
    (V.fromList
      [ FGenericParam 0
      , FArray (callType' (Proxy :: Proxy (Tree.Tree a)) [FGenericParam 0])
      ]
    )
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
