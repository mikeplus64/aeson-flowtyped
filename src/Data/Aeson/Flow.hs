{-# LANGUAGE CPP                       #-}
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
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
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
  , FlowType
  , Fix (..)
  , FlowTypeF (..)
    -- * Code generation
    -- ** Wholesale ES6/flow modules
  , FlowModuleOptions (..)
  , defaultFlowModuleOptions
  , Export (..)
  , generateFlowModule
  , writeFlowModule
  , exportFlowTypeAs
  , flowTypeAs
    -- * Utility functions
  , showFlowType
  , dependencies
  , exportsDependencies
  , FlowTyFields (..)
  , DeconstructField
    -- * Internals
  , defaultFlowType
  , defaultFlowTypeName
  , FlowName (..)
  , PrimType (..)
  , GFlowTyped
  , FlowTypeI
  , Info (..)
  , Var (..)
  , Typeable
  , typeRep
  ) where
import           Control.Monad
import           Control.Monad.Trans.State.Strict
import qualified Data.Aeson                       as A
import           Data.Aeson.Types                 (Options (..),
                                                   SumEncoding (..))
import           Data.Fixed                       (Fixed)
import           Data.Foldable
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
import           Data.Map.Strict                  (Map)
import qualified Data.Map.Strict                  as M
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
import           Data.Maybe
import           Debug.Trace
import           GHC.Generics
import           GHC.TypeLits
import qualified Text.PrettyPrint.Leijen          as PP

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

-- | A primitive flow/javascript type
data PrimType
  = Boolean
  | Number
  | String
  | Void
  | Mixed
  | Any
  deriving (Show, Read, Eq, Ord)

-- | A name for a flowtyped data-type. These are returned by 'dependencies'.
data FlowName where
  FlowName :: (Typeable a, FlowTyped a) => Proxy a -> Text -> FlowName

instance Show FlowName where
  show (FlowName _ t) = show t

instance Eq FlowName where
  FlowName _ n0 == FlowName _ n1 = n0 == n1

instance Ord FlowName where
  FlowName _ n0 `compare` FlowName _ n1 = compare n0 n1

data Flowable where
  Flowable :: (Typeable a, FlowTyped a) => Proxy a -> Flowable

instance Show Flowable where
  show (Flowable t) = show (typeRep t)

instance Eq Flowable where
  Flowable a == Flowable b = typeRep a == typeRep b

-- | The main AST for flowtypes.

data FlowTypeF a
  = Object !(HashMap Text a)
  | ExactObject !(HashMap Text a)
  | ObjectMap !Text a
  | Array a
  | Tuple !(Vector a)
  | Fun !(Vector (Text, a)) a
  | Alt a a
  | Prim !PrimType
  | Nullable a
  | Omitable a
  | Literal !A.Value
  | Tag !Text
  | Name !FlowName
  | Instantiate !TypeRep a
  | PolyVar !TypeRep
  | PolyUse !Flowable
  | PolyApply a [a]
  deriving (Show, Eq, Functor, Traversable, Foldable)
-- XXX: vector >= 0.12 has Eq1 vector which allows us to use eq for Fix FlowTypeF
-- and related types

instance Show1 FlowTypeF where
  liftShowsPrec sp sl i a =
    liftShowsPrec sp sl i (reify sp (\p -> Showy (fmap (inj p) a)))

data Info a = Constr !Text FlowTypeI a | NoInfo a
  deriving (Show, Functor, Traversable, Foldable)

instance Show1 (Showy Info) where
  liftShowsPrec _ _ i (Showy a) = showsPrec i a

instance Show1 Info where
  liftShowsPrec sp sl i a =
    liftShowsPrec sp sl i (reify sp (\p -> Showy (fmap (inj p) a)))

type FlowTypeI = Fix (Info `Compose` FlowTypeF)

type FlowType = Fix FlowTypeF

text :: Text -> PP.Doc
text = PP.text . T.unpack

squotes :: Text -> PP.Doc
squotes = text . T.replace "'" "\\'"

type Poly = State (Map TypeRep Text)

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
          (\fty'' -> text name PP.<> PP.text "?" PP.<> PP.colon PP.<+> fty'') <$> pp fty'
        fty' ->
          (\fty'' -> text name PP.<> PP.colon PP.<+> fty'') <$> pp fty'

getVar :: TypeRep -> Poly Text
getVar rep = do
  s <- get
  case M.lookup rep s of
    Just i -> return i
    Nothing -> do
      let r = polyVarNames !! M.size s
      r <$ modify' (M.insert rep r)

polyVarNames :: [Text]
polyVarNames =
  map T.singleton ['A'..'Z'] ++
  zipWith (\i t -> t `T.append` T.pack (show i)) [0 :: Int ..] polyVarNames

pp :: FlowType -> Poly PP.Doc
pp (Fix ft) = case ft of
  ObjectMap keyName a ->
    (\r -> braceList
      [ PP.brackets (text keyName PP.<> PP.text ": string") PP.<>
        PP.colon PP.<+>
        r
      ]) <$> pp a
  Object hm -> braceList <$> ppObject hm
  ExactObject hm -> braceBarList <$> ppObject hm
  Array a -> (\r -> mayWrap a r PP.<> PP.string "[]") <$> pp a
  Tuple t -> PP.list <$> mapM pp (V.toList t)
  Alt a b -> ppAlts [a] b
  Prim pt -> return $ case pt of
    Boolean -> PP.text "boolean"
    Number  -> PP.text "number"
    String  -> PP.text "string"
    Void    -> PP.text "void"
    Any     -> PP.text "any"
    Mixed   -> PP.text "mixed"
  Nullable a -> (\r -> PP.char '?' PP.<> mayWrap a r) <$> pp a
  Omitable a -> (\r -> PP.char '?' PP.<> mayWrap a r) <$> pp a -- hopefully these are caught
  Literal a -> return (ppJson a)
  Tag t -> return (squotes t)
  Name (FlowName _ t) -> return (text t)
  PolyVar rep -> text <$> getVar rep
  PolyUse (Flowable fp) -> pp (flowType fp)
  PolyApply a vars -> do
    n  <- pp a
    vs <- mapM pp vars
    return (n PP.<> PP.angles (PP.hsep (PP.punctuate PP.comma vs)))
  _ -> return (PP.string (show ft))

-- | Pretty-print a flowtype in flowtype syntax
showFlowType :: FlowType -> Text
showFlowType ft = T.pack (show (evalState (pp ft) M.empty))

--------------------------------------------------------------------------------
-- Module exporting

-- | Generate a @ export type @ declaration.
exportFlowTypeAs :: Text -> FlowType -> Text
exportFlowTypeAs = flowTypeAs True

-- | Generate a @ export type @ declaration.
flowTypeAs :: Bool -> Text -> FlowType -> Text
flowTypeAs isExport name ft =
  T.pack . render $
  PP.string (if isExport then "export type " else "type ") PP.<>
  PP.string (T.unpack name) PP.<> withVars (runState (pp ft) M.empty)
  where
    main r = PP.string "=" PP.<$> PP.indent 2 r PP.<> PP.string ";"
    withVars (r, vars)
      | M.null vars = PP.space PP.<> main r
      | otherwise = PP.angles (PP.hsep
                               (PP.punctuate PP.comma (map text (M.elems vars))))
                    PP.<+>
                    main r
    render = ($[]) . PP.displayS . PP.renderPretty 1.0 80

-- | Compute all the dependencies of a 'FlowTyped' thing, including itself.
dependencies :: (Typeable a, FlowTyped a) => Proxy a -> Set.Set FlowName
dependencies p0 = M.foldlWithKey'
                  (\acc k a -> Set.insert k (Set.union a acc))
                  Set.empty
                  (go p0 M.empty)
  where
    -- XXX: catch mutual recursion
    addImmediateDeps :: FlowName
                     -> Map FlowName (Set.Set FlowName)
                     -> Map FlowName (Set.Set FlowName)
    addImmediateDeps fn@(FlowName p _) acc0 =
      foldr
      (\(FlowName p _) -> go p)
      (M.insert fn sub acc0)
      sub
      where sub = immediateDeps (flowType p)

    go :: (FlowTyped a, Typeable a)
       => Proxy a
       -> Map FlowName (Set.Set FlowName)
       -> Map FlowName (Set.Set FlowName)
    go p acc =
      case FlowName p <$> flowTypeName p of
        Just fn | fn `M.notMember` acc -> addImmediateDeps fn acc
        _                              -> acc

immediateDeps :: FlowType -> Set.Set FlowName
immediateDeps (Fix (Name n)) = Set.singleton n
immediateDeps (Fix p)        = foldMap immediateDeps p

data FlowModuleOptions = FlowModuleOptions
  { -- | You might want to change this to include e.g. flow-runtime
    flowPragmas     :: [Text]
  , flowHeader      :: [Text]
  , flowExportDeps  :: Bool
  , flowComputeDeps :: Bool
  } deriving (Eq, Show)

defaultFlowModuleOptions :: FlowModuleOptions
defaultFlowModuleOptions = FlowModuleOptions
  { flowPragmas = ["// @flow"]
  , flowHeader = ["This module has been generated by aeson-flowtyped."]
  , flowExportDeps = True
  , flowComputeDeps = True
  }

data Export where
  Export :: (Typeable a, FlowTyped a)
         => Proxy a
         -> Export

instance Eq Export where
  Export p0 == Export p1 =
    flowTypeName p0 == flowTypeName p1 ||
    typeRep p0 == typeRep p1

exportsDependencies :: [Export] -> Set.Set FlowName
exportsDependencies = foldMap (\(Export a) -> dependencies a)

generateFlowModule :: FlowModuleOptions -> [Export] -> Text
generateFlowModule opts exports =
  T.unlines
  . (\m ->
       (flowPragmas opts ++ map ("// " `T.append`) (flowHeader opts)) ++
       (T.empty : m))
  . map flowDecl
  . flowNames
  $ exports
  where
    flowNames =
      if flowComputeDeps opts
      then Set.toList . exportsDependencies
      else catMaybes . map (\(Export p) -> FlowName p <$> flowTypeName p)

    flowDecl (FlowName p name) =
      if Export p `elem` exports || flowExportDeps opts
      then flowTypeAs True name (flowType p)
      else flowTypeAs False name (flowType p)

writeFlowModule :: FlowModuleOptions -> FilePath -> [Export] -> IO ()
writeFlowModule opts path =
  TIO.writeFile path . generateFlowModule opts

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
defaultFlowTypeName p = Just (T.pack (symbolVal (pGetName (fmap from p))))
  where
    pGetName :: Proxy (D1 ('MetaData name mod pkg t) c x) -> Proxy name
    pGetName _ = Proxy

flowTypePreferName :: (Typeable a, FlowTyped a) => Proxy a -> FlowType
flowTypePreferName p = fromMaybe (flowType p) (flowTypeRecur p)

flowTypeRecur :: (Typeable a, FlowTyped a) => Proxy a -> Maybe FlowType
flowTypeRecur p = case flowTypeName p of
  Just n
    | null vars -> Just name
    | otherwise -> Just (Fix (PolyApply name (map doPoly vars)))
    where
      doPoly :: TypeRep -> FlowType
      doPoly = Fix . PolyVar

      vars = flowTypeVars p
      name = Fix (Name (FlowName p n))
  Nothing -> Nothing

class FlowTyped a where
  flowType :: Proxy a -> FlowType
  flowTypeName :: Proxy a -> Maybe Text

  flowTypeVars :: Proxy a -> [TypeRep]
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

--------------------------------------------------------------------------------

type family DeconstructField (k :: t) :: (Symbol, Type)
type instance DeconstructField '(a, b) = '(a, b)

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

instance ( DeconstructField x ~ '(k, v)
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
  flowType _ = Fix (ExactObject (reifyFlowTyFields (Proxy :: Proxy fs) H.empty))
  flowTypeName _ = flowTypeName (Proxy :: Proxy a)

--------------------------------------------------------------------------------

class GFlowTyped g where
  gflowType :: Options -> Proxy (g x) -> FlowType

class GFlowVal g where
  gflowVal :: Options -> Proxy (g x) -> FlowTypeI

instance (KnownSymbol name, GFlowVal c) =>
         GFlowTyped (D1 ('MetaData name mod pkg t) c) where
  gflowType opt _ = runFlowI (postprocess (gflowVal opt (Proxy :: Proxy (c x))))
    where
      postprocess :: FlowTypeI -> FlowTypeI
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
          removeSingleConstructorTag :: FlowTypeI -> Maybe FlowTypeI
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
          isNullary :: FlowTypeI -> Bool
          isNullary (FC (Info (Prim Void))) = True
          isNullary _                       = False

          -- try to detect if the type is a bunch of single-constructor
          -- alternatives
          --
          -- XXX: this should preserve the order in which they are declared
          -- ... but does it?
          go :: [Text] -> FlowTypeI -> Maybe [Text]
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

      runFlowI :: FlowTypeI -> FlowType
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

noInfo :: f (Fix (Compose Info f)) -> Fix (Compose Info f)
noInfo = Fix . Compose . NoInfo

infoConstr :: Text -> FlowTypeI -> f (Fix (Compose Info f)) -> Fix (Compose Info f)
infoConstr tag nxt = Fix . Compose . Constr tag nxt

discardInfo :: Info a -> a
discardInfo (NoInfo a)     = a
discardInfo (Constr _ _ a) = a

pattern Info :: a -> Info a
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
        then H.map $ \(Fix t) -> Fix $ case t of
          Nullable a -> Omitable a
          _          -> t
        else id

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

instance (Typeable r, FlowTyped r) => GFlowVal (Rec0 r) where
  gflowVal _opt p = cata noInfo (flowTypePreferName (fmap unK1 p))

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
  gflowVal _ _ = noInfo (Prim Void)

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

instance (Typeable a, FlowTyped a) => FlowTyped [a] where
  flowType _ = Fix (Array (flowTypePreferName (Proxy :: Proxy a)))
  isPrim _ = True
  flowTypeName _ = Nothing

instance (FlowTyped a, Typeable a) => FlowTyped (Vector a) where
  flowType _ = Fix (Array (flowTypePreferName (Proxy :: Proxy a)))
  isPrim _ = True
  flowTypeName _ = Nothing

instance (FlowTyped a, Typeable a) => FlowTyped (VU.Vector a) where
  flowType _ = Fix (Array (flowTypePreferName (Proxy :: Proxy a)))
  isPrim _ = True
  flowTypeName _ = Nothing

instance (FlowTyped a, Typeable a) => FlowTyped (VS.Vector a) where
  flowType _ = Fix (Array (flowTypePreferName (Proxy :: Proxy a)))
  isPrim _ = True
  flowTypeName _ = Nothing

instance ( FlowTyped a, Typeable a
         , FlowTyped b, Typeable b) => FlowTyped (a, b) where
  flowTypeName _ = Nothing
  flowType _ =
    Fix (Tuple (V.fromList [aFt, bFt]))
    where
      aFt = flowTypePreferName (Proxy :: Proxy a)
      bFt = flowTypePreferName (Proxy :: Proxy b)

instance (FlowTyped a, Typeable a) => FlowTyped (Maybe a) where
  flowType _ = Fix (Nullable (flowTypePreferName (Proxy :: Proxy a)))
  isPrim _ = True
  flowTypeName _ = Nothing

instance ( FlowTyped a, Typeable a
         , FlowTyped b, Typeable b) =>
         FlowTyped (Either a b) where
  flowTypeName _ = Nothing
  flowType _ = Fix
    (Alt
     (Fix (ExactObject (H.fromList [("Left", aFt)])))
     (Fix (ExactObject (H.fromList [("Right", bFt)]))))
    where
      aFt = flowTypePreferName (Proxy :: Proxy a)
      bFt = flowTypePreferName (Proxy :: Proxy b)

instance ( FlowTyped a, Typeable a
         , FlowTyped b, Typeable b
         , FlowTyped c, Typeable c) =>
         FlowTyped (a, b, c) where
  flowTypeName _ = Nothing
  flowType _ = Fix (Tuple (V.fromList [aFt, bFt, cFt]))
    where
      aFt = flowTypePreferName (Proxy :: Proxy a)
      bFt = flowTypePreferName (Proxy :: Proxy b)
      cFt = flowTypePreferName (Proxy :: Proxy c)

instance FlowTyped Text where
  isPrim  _ = True
  flowType _ = Fix (Prim String)
  flowTypeName _ = Nothing

instance FlowTyped TL.Text where
  isPrim  _ = True
  flowType _ = Fix (Prim String)
  flowTypeName _ = Nothing

instance {-# OVERLAPS #-} FlowTyped String where
  isPrim  _ = True
  flowType _ = Fix (Prim String)
  flowTypeName _ = Nothing

instance FlowTyped Void.Void where
  isPrim  _ = True
  flowType _ = Fix (Prim Void)
  flowTypeName _ = Nothing

instance FlowTyped Char where
  isPrim  _ = True
  flowType _ = Fix (Prim String)
  flowTypeName _ = Nothing

instance FlowTyped Bool where
  isPrim  _ = True
  flowType _ = Fix (Prim Boolean)
  flowTypeName _ = Nothing

instance FlowTyped A.Value where
  isPrim  _ = True
  flowType _ = Fix (Prim Mixed)
  flowTypeName _ = Nothing

instance FlowTyped UTCTime where
  isPrim  _ = False
  flowType _ = Fix (Prim String)
  flowTypeName _ = Nothing

instance Typeable a => FlowTyped (Fixed a) where
  isPrim  _ = False
  flowType _ = Fix (Prim Number)
  flowTypeName _ = Nothing

-- | This is at odds with "aeson" which defines 'A.ToJSONKey'
instance (Typeable a, FlowTyped a) => FlowTyped (HashMap Text a) where
  -- XXX this is getting quite incoherent, what makes something "Prim" or not...
  isPrim _ = True
  flowType _ = Fix (ObjectMap "key" (flowTypePreferName (Proxy :: Proxy a)))
  flowTypeName _ = Nothing

instance (Typeable a, FlowTyped a) => FlowTyped (Set.Set a) where
  isPrim _ = False
  flowType _ = Fix (Array (flowTypePreferName (Proxy :: Proxy a)))
  flowTypeName _ = Nothing

instance FlowTyped IntSet.IntSet where
  isPrim _ = False
  flowType _ = Fix (Array (Fix (Prim Number)))
  flowTypeName _ = Nothing

instance (Typeable a, FlowTyped a) => FlowTyped (I.IntMap a) where
  isPrim _ = False
  flowType _ = Fix . Array . Fix . Tuple . V.fromListN 2 $
    [ flowType (Proxy :: Proxy Int)
    , flowType (Proxy :: Proxy a)
    ]
  flowTypeName _ = Nothing

instance (Typeable a, FlowTyped a) => FlowTyped (HashSet.HashSet a) where
  isPrim _ = False
  flowType _ = Fix (Array (flowTypePreferName (Proxy :: Proxy a)))
  flowTypeName _ = Nothing

data Var :: k -> Type where Var :: Var a

instance (Typeable a, Typeable k) => FlowTyped (Var (a :: k)) where
  isPrim _ = False
  flowType _ = Fix (PolyVar (typeOf (Var :: Var a)))
  flowTypeName _ = Nothing

-- | This instance is defined recursively. You'll probably need to use
-- 'dependencies' to extract a usable definition
instance (FlowTyped a, Typeable a) => FlowTyped (Tree.Tree a) where
  isPrim _ = False
  flowType _ = Fix (Tuple
                    (V.fromList
                     [ Fix (PolyUse (Flowable (Proxy :: Proxy a)))
                     , Fix (Array
                            (fromJust (flowTypeRecur (Proxy :: Proxy (Tree.Tree a)))))
                     ]))
  flowTypeName _ = Just "Tree"
  flowTypeVars _ = [typeRep (Var :: Var a)]

instance FlowTyped () where
  isPrim _ = False
  flowType _ = Fix (Tuple V.empty)
  flowTypeName _ = Nothing

-- monomorphic numeric instances
$(concat <$> mapM
  (\ty ->
     [d|
      instance FlowTyped $ty where
        isPrim  _ = False
        flowType _ = Fix (Prim Number)
        flowTypeName _ = Nothing |])
  [ [t|Int|], [t|Int8|], [t|Int16|], [t|Int32|], [t|Int64|]
  , [t|Word|], [t|Word8|], [t|Word16|], [t|Word32|], [t|Word64|]
  , [t|Float|], [t|Double|], [t|Scientific|]
  ])
