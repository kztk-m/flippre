{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Text.FliPpr.Internal.ReifySharing (
  reifySharing,
) where

import Control.Exception (assert)
import Control.Monad (unless, when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.RWS (RWS)
import qualified Control.Monad.RWS as RWS
import Control.Monad.Reader (Reader, ReaderT)
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.State as State
import Control.Monad.Writer.CPS (Writer)
import qualified Control.Monad.Writer.CPS as Writer
import Data.Bits (xor)
import Data.Function.Compat (applyWhen)
import qualified Data.Graph.Inductive as FGL
import qualified Data.HashMap.Strict as H
import Data.Hashable (Hashable (..))
import Data.IORef
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.Maybe (fromMaybe)
import qualified Data.RangeSet.List as RS
import qualified Data.Set as S
import Data.Some
import Data.String (IsString (..))
import Debug.Trace (traceIO, traceM)
import qualified Defs as D
import GHC.Stack (CallStack)
import qualified Prettyprinter as PP
import System.IO.Unsafe (unsafePerformIO)
import System.Mem.StableName
import Unsafe.Coerce (unsafeCoerce)

-- import qualified Data.Graph.Inductive.Dot as FGLDot

import Data.GADT.Compare
import Data.GADT.Show (GShow (..), defaultGshowsPrec)
import Data.Type.Equality ((:~:) (..))
import Text.FliPpr.Internal.Core
import Unembedding.Env

reifySharing :: forall s a vv. (Phased s) => (forall v. Exp s v a) -> Exp Explicit vv a
reifySharing e = case phase @s of
  SImplicit -> fromImplicit e
  SExplicit -> e

fromImplicit :: forall vv a. (forall v. Exp Implicit v a) -> Exp Explicit vv a
fromImplicit e = unsafePerformIO $ do
  res <- runAnnotate e
  traceIO "-- After pruning ---------------"
  traceIO $ show $ let (ee, _, _) = res in ee
  traceIO "--------------------------------"
  traceIO $ "OccMap = " <> let (_, om, _) = res in show om
  traceIO $ "DepGraph = " <> let (_, _, gr) = res in show gr
  ne <- introduceLets res
  traceIO "-- After let-introduction ------"
  traceIO $ show ne
  let result :: forall v. Exp Explicit v a
      result = Reader.runReader (unname ne) (H.empty, H.empty)
  traceIO "-- After unnaming ---------------"
  traceIO $ show result
  pure result

data StableExpName a where
  StableExpName ::
    {getStableName :: !(StableName (Exp Implicit Name a))}
    -> StableExpName a
  deriving stock Eq

instance Show (StableExpName a) where
  show (StableExpName x) = "@" ++ show (hashStableName x)

instance GShow StableExpName where
  gshowsPrec = defaultGshowsPrec

instance GEq StableExpName where
  geq (StableExpName x) (StableExpName y)
    | x == unsafeCoerce y = Just (unsafeCoerce Refl)
    | otherwise = Nothing

-- Use the strong assumption that stable names do not rely on the type parameter

-- Abstract label to specify named interpretation.
data Name

-- A phantom type for variable names
newtype instance In Name a = VName Int
type VName = In Name
instance Show (In Name a) where
  show (VName i) = "#" ++ show i

-- Using StableName as a variable name would make debugging hard as we are not
-- able to print its canonical representation. So, we use another phantom type.

newtype ExpName (a :: FType) = ExpName Int
  deriving newtype (Eq, Ord, Hashable)

instance Show (ExpName a) where
  show (ExpName i) = "@" ++ show i

instance GEq ExpName where
  geq (ExpName i) (ExpName j)
    | i == j = Just (unsafeCoerce Refl)
    | otherwise = Nothing

instance GShow ExpName where
  gshowsPrec = defaultGshowsPrec

instance Hashable (Some ExpName) where
  hashWithSalt salt (Some (ExpName en)) = hashWithSalt salt en

newtype FName a = SName (ExpName a)
  deriving stock Eq

instance Show (FName a) where
  show (SName a) = show a

instance GEq FName where
  geq x y
    | x == unsafeCoerce y = Just (unsafeCoerce Refl)
    | otherwise = Nothing

type instance FVar Name = FName

instance Hashable (Some StableExpName) where
  hashWithSalt salt (Some x) = salt `xor` hashStableName (getStableName x)

data NBranch nexp a (t :: FType) where
  NBranch :: !(PartialBij a b) -> !(VName b) -> !(nexp t) -> NBranch nexp a t

instance (forall x. Show (nexp x)) => Show (NBranch nexp a t) where
  show (NBranch (PartialBij s _ _) n e) = show (s, n, e)

-- | Named expressions
data NExpH nexp a where
  NLam :: !(VName a) -> !(nexp b) -> NExpH nexp (a ~> b)
  NApp :: !(nexp (a ~> b)) -> !(VName a) -> NExpH nexp b
  NCase :: !CallStack -> !(VName a) -> ![NBranch nexp a t] -> NExpH nexp t
  NUnPair :: !CallStack -> !(VName (a, b)) -> !(VName a) -> !(VName b) -> !(nexp t) -> NExpH nexp t
  NUnUnit :: !(VName ()) -> !(nexp t) -> NExpH nexp t
  NCharAs :: !(VName Char) -> !(RS.RSet Char) -> NExpH nexp D
  NOp0 :: !NullaryOp -> NExpH nexp D
  NOp1 :: !UnaryOp -> !(nexp D) -> NExpH nexp D
  NOp2 :: !BinaryOp -> !(nexp D) -> !(nexp D) -> NExpH nexp D
  NVar :: !(FName a) -> NExpH nexp a

-- NLocal :: !(def '[] a) -> NExpH nexp def a

deriving stock instance
  (forall t. Show (nexp t)) =>
  Show (NExpH nexp a)

parensWhen :: Bool -> PP.Doc ann -> PP.Doc ann
parensWhen b = applyWhen b PP.parens

prettyNExpH ::
  forall nexp a ann.
  (forall t. Int -> nexp t -> PP.Doc ann)
  -> Int
  -> NExpH nexp a
  -> PP.Doc ann
prettyNExpH pprExp k = \case
  NLam x e ->
    parensWhen (k > 0) $
      PP.hsep [fromString "\\", PP.viaShow x, fromString "->", PP.align $ pprExp 0 e]
  NApp e x ->
    parensWhen (k > 9) $
      PP.hsep [pprExp 9 e, PP.viaShow x]
  NCase _ x brs ->
    parensWhen (k > 0) $
      PP.sep
        [ PP.hsep
            [ fromString "case"
            , PP.viaShow x
            , fromString "of"
            ]
        , PP.braces $ PP.nest 2 $ PP.sep (map pprBranch brs)
        ]
  NUnPair _ x x1 x2 e ->
    parensWhen (k > 0) $
      PP.sep
        [ PP.hsep [fromString "let", PP.parens (PP.viaShow x1 <> PP.comma <> PP.viaShow x2), fromString "=", PP.viaShow x, fromString "in"]
        , PP.align (pprExp 0 e)
        ]
  NUnUnit x e ->
    parensWhen (k > 0) $
      PP.sep
        [ PP.hsep [fromString "let () =", PP.viaShow x, fromString "in"]
        , PP.align (pprExp 0 e)
        ]
  NCharAs x rs ->
    parensWhen (k > 9) $
      PP.hsep [fromString "charAs", PP.viaShow x, PP.parens (PP.viaShow rs)]
  NVar xx -> PP.viaShow xx
  NOp0 op -> case op of
    Line -> fromString "line"
    Line' -> fromString "line'"
    Abort _ -> fromString "abort"
    Space -> fromString "space"
    Spaces -> fromString "spaces"
    LineBreak -> fromString "LineBreak"
    NESpaces' -> fromString "nespaces'"
    Text s ->
      parensWhen (k > 9) $
        PP.hsep [fromString "text", PP.viaShow s]
  NOp1 op e ->
    let d = pprExp 10 e
    in  parensWhen (k > 9) $ case op of
          Group -> PP.nest 2 $ PP.sep [fromString "group", d]
          Nest n -> PP.nest 2 $ PP.sep [PP.hsep [fromString "nest", PP.pretty n], d]
          Align -> PP.nest 2 $ PP.sep [fromString "align", d]
  NOp2 op e1 e2 ->
    case op of
      Cat -> parensWhen (k > 6) $ PP.sep [pprExp 7 e1, PP.hsep [fromString "<#>", pprExp 6 e2]]
      BChoice -> parensWhen (k > 4) $ PP.sep [pprExp 5 e1, PP.hsep [fromString "<?", pprExp 4 e2]]
  where
    pprBranch :: NBranch nexp aa t -> PP.Doc ann
    pprBranch (NBranch (PartialBij s _ _) n e) =
      PP.hsep [fromString s, fromString "$ \\", PP.viaShow n, fromString "->", PP.align $ pprExp 0 e]

data AnnNExp a
  = AnnNExp !(Maybe (ExpName a)) !(NExpH AnnNExp a)
  | AnnNRef !(ExpName a)

instance Show (AnnNExp a) where
  show = show . PP.pretty

instance PP.Pretty (AnnNExp a) where
  pretty = prettyAnnNExp 0
    where
      prettyAnnNExp :: Int -> AnnNExp t -> PP.Doc ann
      prettyAnnNExp k (AnnNExp Nothing e) = prettyNExp k e
      prettyAnnNExp _ (AnnNExp (Just x) e) = PP.hcat [PP.viaShow x, PP.braces (PP.align (prettyNExp 0 e))]
      prettyAnnNExp _ (AnnNRef x) = PP.viaShow x

      prettyNExp = prettyNExpH prettyAnnNExp

type OccMap = H.HashMap (Some ExpName) Int

emptyOccMap :: OccMap
emptyOccMap = H.empty

lookupOccMap :: Some ExpName -> OccMap -> Maybe Int
lookupOccMap = H.lookup

modifyOccMap :: Some ExpName -> (Int -> Int) -> OccMap -> OccMap
modifyOccMap = flip H.adjust

insertOccMap :: Some ExpName -> Int -> OccMap -> OccMap
insertOccMap = H.insert

data AnnConf = AnnConf
  { occMapRef :: !(IORef OccMap)
  , renameMapRef :: !(IORef (H.HashMap (Some StableExpName) Int))
  , nameSourceRef :: !(IORef Int)
  , vnameLevel :: !Int
  , fnameLevel :: !Int
  }

nameStableName :: StableExpName a -> AnnM (ExpName a)
nameStableName sn = do
  ref <- Reader.asks renameMapRef
  m <- liftIO $ readIORef ref
  case H.lookup (Some sn) m of
    Just i -> pure $ ExpName i
    Nothing -> do
      nsref <- Reader.asks nameSourceRef
      cnt <- liftIO $ readIORef nsref
      liftIO $ writeIORef nsref $! cnt + 1
      let !m' = H.insert (Some sn) cnt m
      liftIO $ writeIORef ref m'
      pure $ ExpName cnt

incVNameLevel :: Int -> AnnConf -> AnnConf
incVNameLevel k conf@AnnConf{vnameLevel = n} = conf{vnameLevel = n + k}

type AnnM = ReaderT AnnConf IO

-- TODO:
--  * [x] Suppress sharing of small expressions
--  * [ ] Share texts with the same contents
--  * [ ] CSE

isSmallExp :: Exp Implicit Name a -> Bool
isSmallExp (Op0 (Text _)) = False
isSmallExp (Op0 _) = True
isSmallExp _ = False

annotate :: forall a. Exp Implicit Name a -> AnnM (AnnNExp a)
annotate !e0 = do
  ref <- Reader.asks occMapRef
  occMap <- liftIO $ readIORef ref
  n <- liftIO $ makeStableName e0
  expName@(ExpName cID) <- nameStableName (StableExpName n)
  let key = Some expName
  case lookupOccMap key occMap of
    Just _ -> do
      -- Case: we already have encountered the expression
      liftIO $ modifyIORef' ref $ modifyOccMap key succ
      pure $ AnnNRef expName
    Nothing -> do
      -- Case: the first time we see exp
      let isSmall = isSmallExp e0
      unless isSmall $ liftIO $ modifyIORef' ref $ insertOccMap key 1
      let wrap = AnnNExp (if isSmall then Nothing else Just expName)
      fmap wrap (go cID e0)
  where
    go cID = \case
      Op0 op ->
        pure (NOp0 op)
      Op1 op e ->
        NOp1 op <$> annotate e
      Op2 op e1 e2 ->
        NOp2 op <$> annotate e1 <*> annotate e2
      Lam h -> do
        level <- Reader.asks vnameLevel
        let vn = VName level
        let e = h vn
        NLam vn <$> Reader.local (incVNameLevel 1) (annotate e)
      App e x -> do
        NApp <$> annotate e <*> pure x
      UnUnit x e -> do
        NUnUnit x <$> annotate e
      UnPair cs x h -> do
        level <- Reader.asks vnameLevel
        let v1 = VName level
        let v2 = VName $ level + 1
        let e = h v1 v2
        NUnPair cs x v1 v2 <$> Reader.local (incVNameLevel 1) (annotate e)
      CharAs x rs ->
        pure $ NCharAs x rs
      Case cs x brs ->
        NCase cs x <$> mapM annotateBranch brs
      Local (DefRet e) -> go cID e
      Var x -> pure $ NVar x

annotateBranch ::
  forall a t.
  Branch VName (Exp Implicit Name) a t
  -> AnnM (NBranch AnnNExp a t)
annotateBranch (Branch pij h) = do
  level <- Reader.asks vnameLevel
  let v1 = VName level
  Reader.local (incVNameLevel 1) $ NBranch pij v1 <$> annotate (h v1)

-- [NOTE] Treatment of depths.
--
-- For an expression with the nesting structure
--
--               |
--         +-----+-----+
--         |           |
--     +---+---+       1
--     |       |
--  +--2--+ +--1--+
--  |     | |     |
--  |     | |  2  |
--  +---- + +-----+
--
-- We introduce the dependency that 1 > 2 to mean that the `let` introduction
-- for 1 is deferred after the introduction of `let` for 2.
--
-- An exception is that all occurrences of 2 appear in the body of 1. Then,
-- there is no dependency between 1 and 2: even when 2 is floated out due to
-- other references in its body, there is no problem with scopes.

makeGraph :: (FGL.DynGraph gr) => Int -> [(Int, Int)] -> (Int -> Bool) -> gr [Some ExpName] ()
makeGraph maxID edges isRelev =
  let g0 =
        FGL.mkGraph
          [(i, i) | i <- [0 .. maxID - 1], isRelev i]
          [(i, j, ()) | (i, j) <- edges]
      g1 = FGL.condensation g0
  in  FGL.nmap (map (Some . ExpName)) g1

type DepGraph = FGL.Gr [Some ExpName] ()

newtype MOccMap = MOccMap OccMap

instance Semigroup MOccMap where
  (MOccMap m1) <> (MOccMap m2) = MOccMap $ H.unionWith (+) m1 m2

instance Monoid MOccMap where
  mempty = MOccMap H.empty

isRelevant :: OccMap -> Some ExpName -> Bool
isRelevant = flip H.member

gatherDep :: OccMap -> AnnNExp a -> Writer (MOccMap, IS.IntSet, S.Set (Int, Int)) (AnnNExp a)
gatherDep occMap (AnnNRef n@(ExpName i)) = do
  let key = Some n
  when (isRelevant occMap key) $
    Writer.tell (MOccMap $ insertOccMap key 1 emptyOccMap, IS.singleton i, S.empty)
  pure (AnnNRef n)
gatherDep occMap (AnnNExp msn e0) = Writer.pass $ do
  (e0', (MOccMap oMap, names, edges)) <- Writer.listen (go e0)
  let (msn', oMap', names') = case msn of
        Just sn@(ExpName i)
          | isRelevant occMap (Some sn) ->
              (Just sn, H.insertWith (+) (Some sn) 1 oMap, IS.insert i names)
        _ -> (Nothing, oMap, names)
  let satNames =
        [ i
        | k@(Some (ExpName i)) <- H.keys oMap'
        , let cnt1 = fromMaybe 0 (H.lookup k occMap)
        , let cnt2 = fromMaybe 0 (H.lookup k oMap')
        , cnt1 == cnt2
        ]
  case msn' of Just (ExpName i) -> traceM $ "Looked: " ++ show i; _ -> pure ()
  let names'' = names' IS.\\ IS.fromList satNames
  let newEdges = case msn' of
        Just (ExpName i) -> [(i, j) | j <- IS.toList names'']
        _ -> []
  pure (AnnNExp msn' e0', const (MOccMap oMap', names'', S.fromAscList newEdges `S.union` edges))
  where
    go :: NExpH AnnNExp a -> Writer (MOccMap, IS.IntSet, S.Set (Int, Int)) (NExpH AnnNExp a)
    go = \case
      NOp0 op -> pure (NOp0 op)
      NOp1 op e -> NOp1 op <$> gatherDep occMap e
      NOp2 op e1 e2 ->
        NOp2 op
          <$> gatherDep occMap e1
          <*> gatherDep occMap e2
      NLam x e -> NLam x <$> gatherDep occMap e
      NApp e x -> NApp <$> gatherDep occMap e <*> pure x
      NCase cs x brs ->
        NCase cs x
          <$> sequence [NBranch pij y <$> gatherDep occMap e | NBranch pij y e <- brs]
      NUnPair cs xy x y e -> NUnPair cs xy x y <$> gatherDep occMap e
      NUnUnit x e -> NUnUnit x <$> gatherDep occMap e
      NCharAs x rs -> pure (NCharAs x rs)
      NVar x -> pure (NVar x)

runAnnotate ::
  Exp Implicit Name a -> IO (AnnNExp a, OccMap, DepGraph)
runAnnotate e = do
  let r = annotate e
  ref <- newIORef emptyOccMap
  nsref <- newIORef 0
  rnmapref <- newIORef H.empty
  e' <-
    Reader.runReaderT
      r
      AnnConf
        { occMapRef = ref
        , renameMapRef = rnmapref
        , nameSourceRef = nsref
        , vnameLevel = 0
        , fnameLevel = 0
        }
  occMap <- readIORef ref
  maxIDPlusOne <- readIORef nsref
  let filteredOccMap = H.filter (> 1) occMap

  let (e'', (_, _, edges)) = Writer.runWriter (gatherDep filteredOccMap e')

  traceIO $ "Dependencies: " ++ show (S.toList edges)

  let gr = makeGraph maxIDPlusOne (S.toList edges) $ \n -> Some (ExpName n) `H.member` filteredOccMap
  -- writeFile "_dep.dot" (FGLDot.showDot $ FGLDot.fglToDotString $ FGL.nemap show (const "") gr)

  pure (e'', filteredOccMap, gr)

-- >>> let r = Op2 Cat r (Op0 Space)
-- >>> res <- runAnnotate r
-- >>> res
-- >>> introduceLets res
-- (@0{@0 <#> space},fromList [(@0,2)],mkGraph [(1,[@0])] [])
-- let @0 = @0 <#> space in
-- @0

-- >>> res <- runAnnotate $ let r = Op0 (Text "A") in Op2 Cat r r
-- >>> res
-- >>> introduceLets res
-- (@1{text "A"} <#> @1,fromList [(@1,2)],mkGraph [(1,[@1])] [])
-- let @1 = text "A" in
-- @1 <#> @1

-- >>> res <- runAnnotate $ let r = Op0 (Text "A") in Lam $ \v -> UnUnit v $ Op2 Cat r r
-- >>> res
-- >>> introduceLets res
-- (\ #0 -> let () = #0 in @3{text "A"} <#> @3,fromList [(@3,2)],mkGraph [(1,[@3])] [])
-- \ #0 -> let () = #0 in let @3 = text "A" in @3 <#> @3

-- >>> let { t = Op2 Cat t1 t' ; t' = Op2 Cat t2 t ; t1 = Op0 (Text "A"); t2 = Op2 Cat t1 (Op0 (Text "B")) }
-- >>> res <- runAnnotate t
-- >>> res
-- >>> ne <- introduceLets res
-- >>> ne
-- >>> Reader.runReader (unname ne) (H.empty, H.empty)
-- (@0{@1{text "A"} <#> (@1 <#> text "B") <#> @0},fromList [(@0,2),(@1,2)],mkGraph [(1,[@1]),(2,[@0])] [])
-- let
--   @1 = text "A"
--   @0 = @1 <#> (@1 <#> text "B") <#> @0
-- in @0
-- let
--   f_0 = text "A"
--   f_1 = hcat [f_0, f_0 <#> text "B", f_1]
-- in f_1

-- >>> let { t = Lam $ \x -> let pp = Op2 BChoice (UnUnit x (fromString "A")) (Op2 Cat (fromString "B") pp) in pp }
-- >>> res <- runAnnotate t
-- >>> res
-- >>> introduceLets res
-- (\ #0 -> @1{(let () = #0 in text "A") <? text "B" <#> @1},fromList [(@1,2)],mkGraph [(1,[@1])] [])
-- \ #0 -> let @1 = (let () = #0 in text "A") <? text "B" <#> @1 in
--         @1

-- >>> let { t = Lam $ \x -> let pp = Op2 BChoice (UnUnit x (App t x)) (Op2 Cat (fromString "B") pp) in pp }
-- >>> res <- runAnnotate t
-- >>> res
-- >>> introduceLets res
-- (@0{\ #0 -> @1{(let () = #0 in @0 #0) <? text "B" <#> @1}},fromList [(@0,2),(@1,2)],mkGraph [(1,[@1]),(2,[@0])] [(1,2,())])
-- let @0 = \ #0 -> let @1 = (let () = #0 in @0 #0) <? text "B" <#> @1 in
--                  @1 in
-- @0

_example4 :: Exp Implicit v D
_example4 =
  let x = text "A" in let y = x <#> text "B" in (x <#> y) <#> y
  where
    (<#>) = Op2 Cat
    text = Op0 . Text

-- >>> res <- runAnnotate _example4
-- >>> res
-- >>> introduceLets res
-- ((@2{text "A"} <#> @3{@2 <#> text "B"}) <#> @3,fromList [(@2,2),(@3,2)],mkGraph [(1,[@3]),(2,[@2])] [(1,2,())])
-- let @2 = text "A" in
-- let @3 = @2 <#> text "B" in
-- (@2 <#> @3) <#> @3

_example5 :: Exp Implicit v D
_example5 =
  let x = text "A" <#> text "B" in let y = let z = x <#> text "C" in text "D" <#> z <#> z in x <#> y <#> y
  where
    (<#>) = Op2 Cat
    text = Op0 . Text

-- >>> res <- runAnnotate _example5
-- >>> ne <- introduceLets res
-- >>> res
-- >>> ne
-- >>> Reader.runReader (unname ne) (H.empty, H.empty)
-- ((@2{text "A" <#> text "B"} <#> @5{(text "D" <#> @8{@2 <#> text "C"}) <#> @8})
-- <#> @5,fromList [(@2,2),(@5,2),(@8,2)],mkGraph [(1,[@8]),(2,[@5]),(3,[@2])] [(1,3,()),(2,3,())])
-- let @2 = text "A" <#> text "B" in
-- let @5 = let @8 = @2 <#> text "C" in
--            (text "D" <#> @8) <#> @8 in
-- (@2 <#> @5) <#> @5
-- let f_0 = text "A" <#> text "B" in
-- let f_1 = let f_2 = f_0 <#> text "C" in (text "D" <#> f_2) <#> f_2 in
-- (f_0 <#> f_1) <#> f_1

data RecNExp a
  = RecNExp !(NExpH RecNExp a)
  | NLetRec ![NDefPair] !(RecNExp a)

instance Show (RecNExp a) where
  show = show . PP.pretty

instance PP.Pretty (RecNExp a) where
  pretty = prettyRecNExp 0

prettyRecNExp :: Int -> RecNExp t -> PP.Doc ann
prettyRecNExp k (RecNExp e) = prettyExpInRecNExp k e
prettyRecNExp k (NLetRec [NDefPair x xe] e) =
  parensWhen (k > 0) $
    PP.vsep
      [ PP.hsep [fromString "let", PP.viaShow x, fromString "=", PP.align (PP.nest 2 $ prettyRecNExp 0 xe), fromString "in"]
      , PP.align $ prettyRecNExp 0 e
      ]
prettyRecNExp k (NLetRec defs e) =
  parensWhen (k > 0) $
    PP.vsep
      [ PP.nest 2 $
          PP.vsep
            [ fromString "let"
            , PP.vsep [PP.hsep [PP.viaShow x, fromString "=", PP.align $ PP.nest 2 $ prettyRecNExp 0 xe] | NDefPair x xe <- defs]
            ]
      , PP.hsep [fromString "in", PP.align $ prettyRecNExp 0 e]
      ]

prettyExpInRecNExp :: Int -> NExpH RecNExp a -> PP.Doc ann
prettyExpInRecNExp = prettyNExpH prettyRecNExp

data NDefPair where
  NDefPair :: !(FName a) -> !(RecNExp a) -> NDefPair

deriving stock instance Show NDefPair

splitDefs ::
  [NDefPair]
  -> (forall as. Env FName as -> Env RecNExp as -> r)
  -> r
splitDefs [] k = k ENil ENil
splitDefs (NDefPair x e : defs) k =
  splitDefs defs $ \xs es -> k (x :. xs) (e :. es)

type DefMap = H.HashMap (Some ExpName) (Some RecNExp)

lookupDefMap :: ExpName a -> DefMap -> Maybe (RecNExp a)
lookupDefMap n m = case H.lookup (Some n) m of
  Just (Some v) -> Just (unsafeCoerce v)
  Nothing -> Nothing

insertDefMap :: ExpName a -> RecNExp a -> DefMap -> DefMap
insertDefMap n e = H.insert (Some n) (Some e)

emptyDefMap :: DefMap
emptyDefMap = H.empty

instance Semigroup LMaps where
  LMaps{loccMap = o1, ldefMap = d1} <> LMaps{loccMap = o2, ldefMap = d2} =
    LMaps{loccMap = H.unionWith (+) o1 o2, ldefMap = H.union d1 d2}

instance Monoid LMaps where
  mempty = LMaps{loccMap = emptyOccMap, ldefMap = emptyDefMap}

data LMaps
  = LMaps
  { loccMap :: !OccMap
  , ldefMap :: !DefMap
  }

type Frontier = IM.IntMap [Some ExpName]

type LetIntroM = RWS () LMaps (DepGraph, Frontier)

makeFrontier :: DepGraph -> Frontier
makeFrontier depGr = IM.fromList [(n, nlab) | n <- FGL.nodes depGr, FGL.indeg depGr n == 0, Just nlab <- [FGL.lab depGr n]]

introduceLets ::
  (AnnNExp a, OccMap, DepGraph) -> IO (RecNExp a)
introduceLets (e, occMap, depGr) = do
  -- let fr = IM.fromList [(n, nlab) | (_, n, nlab, _) <- FGL.gsel (\(inE, _, _, _) -> null inE) depGr]
  let fr = makeFrontier depGr
  putStrLn ("Graph: " <> show depGr)
  putStrLn ("Frontier: " <> show fr)
  let (res, _, m) = RWS.runRWS (introLets occMap e) () (depGr, fr)
  let _occRest = H.filter (> 1) $ loccMap m
  print _occRest
  assert (H.null _occRest) (pure res)

makeDefNames ::
  DepGraph
  -> (Some ExpName -> Bool)
  -> Frontier
  -> (DepGraph, Frontier, [[Some ExpName]])
makeDefNames depGr cond fr
  | IM.null fr = (depGr, fr, [])
  | IM.null toProc = (depGr, fr, [])
  | otherwise =
      let dNames = concat $ IM.elems toProc
          (depGr1, fr1) = next toProc
          (depGr2, fr2, dNames') = makeDefNames depGr1 cond fr1
      in  (depGr2, IM.union fr2 rest, dNames : dNames')
  where
    (toProc, rest) = IM.partition (all cond) fr

    next :: Frontier -> (DepGraph, Frontier)
    next fr0 =
      let rmNodes = IM.keys fr0
          depGr' = FGL.delNodes rmNodes depGr
      in  (depGr', makeFrontier depGr')

introLets ::
  OccMap
  -> AnnNExp a
  -> LetIntroM (RecNExp a)
introLets _occMap (AnnNRef sn) = do
  let key = Some sn
  Writer.tell LMaps{loccMap = insertOccMap key 1 emptyOccMap, ldefMap = emptyDefMap}
  pure $ RecNExp $ NVar (SName sn)
introLets occMap (AnnNExp msn e0) = Writer.pass $ do
  (ebody, LMaps{loccMap = count, ldefMap = dMap}) <- Writer.listen $ go e0
  -- Update `count'` first to include this occurrence of `sn`
  let count' = case msn of
        Just sn -> H.insertWith (+) (Some sn) 1 count
        _ -> count
  -- `checkCnt k` tells if there is no occurrences of `k` upwards.
  let checkCnt k =
        let cnt1 = fromMaybe 0 $ lookupOccMap k occMap
            cnt2 = fromMaybe 0 $ lookupOccMap k count'
        in  cnt1 == cnt2
  (dg, fr) <- State.get
  traceM (show fr)
  -- Names to be defined here
  let (dg', fr', defNames_) = makeDefNames dg checkCnt fr
  let defNames = reverse defNames_
  let flatDefNames = concat defNames
  let defs = flip map defNames $ map $ \(Some x) -> case lookupDefMap x dMap of
        Just e -> NDefPair (SName x) e
        _ | Just sn <- msn, Some x == Some sn -> NDefPair (SName sn) (RecNExp ebody)
        _ | otherwise -> error "introLets: cannot happen"
  let bodyExp = nletrecs defs ebody
  let dMap'
        | Just sn <- msn =
            if Some sn `elem` flatDefNames
              then insertDefMap sn (nletrecs [] ebody) dMap
              else insertDefMap sn bodyExp dMap
        | otherwise = dMap
  let dMap'' = foldr H.delete dMap' flatDefNames
  let resExp
        | Just sn <- msn =
            if Some sn `elem` flatDefNames
              then nletrecs defs $ NVar (SName sn)
              else nletrecs [] $ NVar (SName sn)
        | otherwise = bodyExp
  let count'' = foldr H.delete count' flatDefNames
  State.put (dg', fr')
  pure (resExp, const $ LMaps{loccMap = count'', ldefMap = dMap''})
  where
    nletrec [] = id
    nletrec defs = NLetRec defs

    nletrecs [] = RecNExp
    nletrecs (ds : dss) = nletrec ds . nletrecs dss

    go :: NExpH AnnNExp a -> LetIntroM (NExpH RecNExp a)
    go (NLam x e) = NLam x <$> introLets occMap e
    go (NApp e x) = NApp <$> introLets occMap e <*> pure x
    go (NCase cs x brs) = NCase cs x <$> mapM goBranch brs
    go (NUnPair cs x y1 y2 e) = NUnPair cs x y1 y2 <$> introLets occMap e
    go (NUnUnit x e) = NUnUnit x <$> introLets occMap e
    go (NCharAs x rs) = pure $ NCharAs x rs
    go (NOp0 op) = pure $ NOp0 op
    go (NOp1 op e) = NOp1 op <$> introLets occMap e
    go (NOp2 op e1 e2) = NOp2 op <$> introLets occMap e1 <*> introLets occMap e2
    go (NVar x) = pure $ NVar x -- x should be FName i
    -- go (NLocal (AnnNDef d)) = NLocal . RecNDef <$> goDef d
    goBranch :: NBranch AnnNExp b a -> LetIntroM (NBranch RecNExp b a)
    goBranch (NBranch pij b e) = NBranch pij b <$> introLets occMap e

-- goDef :: NDefH AnnNExp AnnNDef as r -> Writer LMaps (NDefH RecNExp RecNDef as r)
-- goDef (NDefRet e) = NDefRet <$> introLets occMap e
-- goDef (NDefCons e (AnnNDef d)) = NDefCons <$> introLets occMap e <*> (RecNDef <$> goDef d)
-- goDef (NDefLetr x (AnnNDef d)) = NDefLetr x . RecNDef <$> goDef d

instance Hashable (Some FName) where
  hashWithSalt salt (Some (SName n)) = hashWithSalt salt n

type VMap v = H.HashMap Int (Some (In v))
type FMap v = H.HashMap (Some FName) (Some (Exp Explicit v))

insertVMap :: VName a -> In v a -> VMap v -> VMap v
insertVMap (VName i) x = H.insert i (Some x)

lookupVMap :: VName a -> VMap v -> Maybe (In v a)
lookupVMap (VName i) vMap = case H.lookup i vMap of
  Just (Some v) -> Just (unsafeCoerce v)
  Nothing -> Nothing

insertFMap :: FName a -> Exp Explicit v a -> FMap v -> FMap v
insertFMap fn f = H.insert (Some fn) (Some f)

lookupFMap :: FName a -> FMap v -> Maybe (Exp Explicit v a)
lookupFMap fn fMap = case H.lookup (Some fn) fMap of
  Just (Some e) -> Just (unsafeCoerce e)
  Nothing -> Nothing

type UnnameM v = Reader (VMap v, FMap v)

_showEnv :: (forall a. Show (f a)) => Env f as -> String
_showEnv ENil = "ENil"
_showEnv (x :. xs) = show x <> " :. " <> _showEnv xs

unname :: RecNExp a -> UnnameM v (Exp Explicit v a)
unname (RecNExp e) = unnameWork e
unname (NLetRec defs e) = Reader.reader $ \(vMap, fMap) ->
  splitDefs defs $ \xs es ->
    letrec
      xs
      ( \xxs ->
          -- trace ("Extended fmap: " ++ _showEnv xs) $
          let fMap' = extendMap xs xxs fMap
              es' = mapEnv (\ei -> Reader.runReader (unname ei) (vMap, fMap')) es
              e' = Reader.runReader (unname e) (vMap, fMap')
          in  (es', e')
      )

letrec :: (D.Defs f) => Env proxy as -> (Env f as -> (Env f as, f r)) -> f r
letrec sh h = D.local $ letrecM sh (pure . h)

letrecM :: (D.Defs f) => Env proxy as -> (Env f as -> D.DefM f (Env f as, res)) -> D.DefM f res
letrecM ENil h = snd <$> h ENil
letrecM (ECons _ sh) h =
  D.letr1 $ \x -> letrecM sh $ \xs -> do
    (vvs, r) <- h (ECons x xs)
    case vvs of
      ECons v vs -> pure (vs, (v, r))

extendMap :: Env FName as -> Env (Exp Explicit v) as -> FMap v -> FMap v
extendMap ENil ENil fMap = fMap
extendMap (x :. xs) (e :. es) fMap = extendMap xs es (insertFMap x e fMap)

-- unnameDef :: RecNDef as r -> UnnameM v (Def Explicit v as r)
-- unnameDef (RecNDef d0) = case d0 of
--   NDefRet e -> DefRet <$> unname e
--   NDefCons e d -> DefCons <$> unname e <*> unnameDef d
--   NDefLetr f d -> do
--     (vMap, fMap) <- Reader.ask
--     pure $ DefLetr $ \ff ->
--       let fMap' = insertFMap f (Var ff) fMap
--       in  Reader.runReader (unnameDef d) (vMap, fMap')

unnameWork :: NExpH RecNExp a -> UnnameM v (Exp Explicit v a)
unnameWork e0 = case e0 of
  NVar f -> do
    (_, fMap) <- Reader.ask
    case lookupFMap f fMap of
      Just v -> pure v
      Nothing ->
        error $
          show $
            PP.vcat
              [ fromString "unnname: IMPOSSIBLE."
              , fromString " - Unreferenced variable" PP.<+> PP.align (PP.viaShow f)
              ]
  -- error $ Text.printf "unname: IMPOSSIBLE. Unreferenced variable: %s." (show f)
  NLam x e -> do
    (vMap, fMap) <- Reader.ask
    pure $ Lam $ \xx ->
      let vMap' = insertVMap x xx vMap
      in  Reader.runReader (unname e) (vMap', fMap)
  NApp e x -> do
    xx <- resolveVar x
    e' <- unname e
    case e' of
      Lam h -> pure $ h xx
      _ -> pure $ App e' xx
  NUnPair cs x y1 y2 e -> do
    xx <- resolveVar x
    (vMap, fMap) <- Reader.ask
    pure $ UnPair cs xx $ \yy1 yy2 ->
      let vMap' = insertVMap y1 yy1 $ insertVMap y2 yy2 vMap
      in  Reader.runReader (unname e) (vMap', fMap)
  NUnUnit x e -> do
    xx <- resolveVar x
    UnUnit xx <$> unname e
  NCharAs x rs -> do
    xx <- resolveVar x
    pure $ CharAs xx rs
  NOp0 op -> pure $ Op0 op
  NOp1 op e -> Op1 op <$> unname e
  NOp2 op e1 e2 -> Op2 op <$> unname e1 <*> unname e2
  NCase cs x brs -> do
    xx <- resolveVar x
    let f (NBranch pij y e) = do
          (vMap, fMap) <- Reader.ask
          pure $ Branch pij $ \yy ->
            let vMap' = insertVMap y yy vMap
            in  Reader.runReader (unname e) (vMap', fMap)
    Case cs xx <$> mapM f brs
    -- NLocal d -> Local <$> unnameDef d
  where
    resolveVar :: forall v x. VName x -> UnnameM v (In v x)
    resolveVar x = do
      (vMap, _) <- Reader.ask
      case lookupVMap x vMap of
        Just xx -> pure xx
        _ ->
          error $
            unlines
              [ "unname: open expression detected."
              , " - unbound var: " ++ show x
              , show (fromString " - In: " <> PP.align (prettyExpInRecNExp 0 e0))
              ]
