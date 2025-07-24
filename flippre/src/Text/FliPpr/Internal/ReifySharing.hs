{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
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

import Control.Monad.Reader (Reader, ReaderT)
import qualified Control.Monad.Reader as Reader
import Data.Bits (xor)
import qualified Data.HashMap.Strict as H
import Data.Hashable (Hashable (..))
import Data.IORef
import Data.Kind (Type)
import qualified Data.RangeSet.List as RS
import System.Mem.StableName

import Text.FliPpr.Internal.Core

import Control.Monad.Writer (Writer)
import qualified Control.Monad.Writer as Writer
import Data.Maybe (fromMaybe)
import Debug.Trace (traceM, traceShowM)
import qualified Defs as D
import GHC.Stack (CallStack)
import System.IO.Unsafe (unsafePerformIO)
import Unembedding.Env
import Unsafe.Coerce (unsafeCoerce)

reifySharing :: forall s a vv. (Phased s) => (forall v. Exp s v a) -> Exp Explicit vv a
reifySharing e = case phase @s of
  SImplicit -> fromImplicit e
  SExplicit -> e

fromImplicit :: forall vv a. (forall v. Exp Implicit v a) -> Exp Explicit vv a
fromImplicit e = unsafePerformIO $ do
  res <- runAnnotate e
  traceM "-- After pruning ---------------"
  traceShowM res
  let ne = introduceLets res
  traceM "-- After let-introduction ------"
  traceShowM ne
  let result :: forall v. Exp Explicit v a
      result = Reader.runReader (unname ne) (H.empty, H.empty)
  traceM "-- After unnaming ---------------"
  traceShowM result
  pure result

-- _ = AnnNExp @1
--   (
--     NLocal (
--       AnnNDef (
--         NDefLetr %0 (AnnNDef (NDefCons (AnnNExp @2 (NOp2 BChoice (AnnNExp @3 (NOp0 (Text ""))) (AnnNExp @4 (NOp2 Cat (AnnNExp @5 (NOp0 Space)) (AnnNExp @6 (NVar %0))))))
--                                        (AnnNDef (NDefRet (AnnNRef @6)))))
--         )
--     )
--   )

data StableExpName a where
  StableExpName ::
    {getStableName :: StableName (Exp Implicit Name a)}
    -> StableExpName a
  deriving stock Eq

instance Show (StableExpName a) where
  show (StableExpName x) = "@" ++ show (hashStableName x)

-- Abstract label to specify named interpretation.
data Name

-- A phantom type for variable names
newtype instance In Name a = VName Int
type VName = In Name
instance Show (In Name a) where
  show (VName i) = "#" ++ show i

data FName a where
  FName :: !Int -> FName a
  SName :: (StableExpName a) -> FName a
  deriving stock Eq

instance Show (FName a) where
  show (FName i) = "%" ++ show i
  show (SName a) = show a

type instance FVar Name = FName

data SomeStableExpName where
  SomeStableExpName :: StableExpName a -> SomeStableExpName

instance Show SomeStableExpName where
  show (SomeStableExpName x) = "@" ++ show (hashStableName (getStableName x))

instance Eq SomeStableExpName where
  SomeStableExpName (StableExpName x) == SomeStableExpName (StableExpName y) =
    -- Use the strong assumption that stable names do not rely on the type parameter
    x == unsafeCoerce y

instance Hashable SomeStableExpName where
  hashWithSalt salt (SomeStableExpName x) =
    salt `xor` hashStableName (getStableName x)

data NBranch nexp a (t :: FType) where
  NBranch :: PartialBij a b -> VName b -> nexp t -> NBranch nexp a t

instance (forall x. Show (nexp x)) => Show (NBranch nexp a t) where
  show (NBranch (PartialBij s _ _) n e) = show (s, n, e)

-- | Named expressions
data NExpH nexp (def :: [FType] -> FType -> Type) a where
  NLam :: !(VName a) -> !(nexp b) -> NExpH nexp def (a ~> b)
  NApp :: !(nexp (a ~> b)) -> !(VName a) -> NExpH nexp def b
  NCase :: CallStack -> !(VName a) -> [NBranch nexp a t] -> NExpH nexp def t
  NUnPair :: CallStack -> !(VName (a, b)) -> !(VName a) -> !(VName b) -> !(nexp t) -> NExpH nexp def t
  NUnUnit :: !(VName ()) -> !(nexp t) -> NExpH nexp def t
  NCharAs :: !(VName Char) -> !(RS.RSet Char) -> NExpH nexp def D
  NOp0 :: !NullaryOp -> NExpH nexp def D
  NOp1 :: !UnaryOp -> !(nexp D) -> NExpH nexp def D
  NOp2 :: !BinaryOp -> !(nexp D) -> !(nexp D) -> NExpH nexp def D
  NVar :: !(FName a) -> NExpH nexp def a

-- NLocal :: !(def '[] a) -> NExpH nexp def a

deriving stock instance
  (forall t. Show (nexp t), forall as r. Show (def as r)) =>
  Show (NExpH nexp def a)

data NDefH nexp def (as :: [FType]) (r :: FType) where
  NDefRet :: !(nexp r) -> NDefH nexp def '[] r
  NDefCons :: !(nexp a) -> !(def as r) -> NDefH nexp def (a : as) r
  NDefLetr :: !(FName a) -> !(def (a : as) r) -> NDefH nexp def as r

deriving stock instance
  (forall t. Show (nexp t), forall as r. Show (def as r)) =>
  Show (NDefH nexp def as' r')

data AnnNExp a
  = AnnNExp !(StableExpName a) !(NExpH AnnNExp AnnNDef a)
  | AnnNRef !(StableExpName a)
  deriving stock Show

newtype AnnNDef as r = AnnNDef (NDefH AnnNExp AnnNDef as r)
  deriving stock Show

type OccMap = H.HashMap SomeStableExpName Int

emptyOccMap :: OccMap
emptyOccMap = H.empty

lookupOccMap :: SomeStableExpName -> OccMap -> Maybe Int
lookupOccMap = H.lookup

modifyOccMap :: SomeStableExpName -> (Int -> Int) -> OccMap -> OccMap
modifyOccMap = flip H.adjust

insertOccMap :: SomeStableExpName -> Int -> OccMap -> OccMap
insertOccMap = H.insert

data Conf = Conf
  { occMapRef :: IORef OccMap
  , vnameLevel :: Int
  , fnameLevel :: Int
  }

incVNameLevel :: Int -> Conf -> Conf
incVNameLevel k conf@Conf{vnameLevel = n} = conf{vnameLevel = n + k}

-- incFNameLevel :: Int -> Conf -> Conf
-- incFNameLevel k conf@Conf{fnameLevel = n} = conf{fnameLevel = n + k}

type AnnM = ReaderT Conf IO

annotate :: forall a. Exp Implicit Name a -> AnnM (AnnNExp a)
annotate !e0 = do
  ref <- Reader.asks occMapRef
  occMap <- Reader.lift $ readIORef ref
  n <- Reader.lift $ makeStableName e0
  let sn = StableExpName n
  let key = SomeStableExpName sn
  case lookupOccMap key occMap of
    Just _ -> do
      -- Case: we already have encountered the expression
      Reader.lift $ modifyIORef' ref $ modifyOccMap key succ
      pure $ AnnNRef sn
    Nothing -> do
      -- Case: the first time we see exp
      Reader.lift $ modifyIORef' ref $ insertOccMap key 1
      let wrap = AnnNExp sn
      fmap wrap (go e0)
  where
    go = \case
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
      Local (DefRet e) -> go e
      Var x -> pure $ NVar x

annotateBranch ::
  forall a t.
  Branch VName (Exp Implicit Name) a t
  -> AnnM (NBranch AnnNExp a t)
annotateBranch (Branch pij h) = do
  level <- Reader.asks vnameLevel
  let v1 = VName level
  Reader.local (incVNameLevel 1) $ NBranch pij v1 <$> annotate (h v1)

-- annotateDef ::
--   Def Implicit Name as r
--   -> AnnM (AnnNDef as r)
-- annotateDef =
--   fmap AnnNDef . \case
--     DefRet e -> NDefRet <$> annotate e
--     DefCons e d -> NDefCons <$> annotate e <*> annotateDef d
--     DefLetr h -> do
--       level <- Reader.asks fnameLevel
--       let f1 = FName level
--       Reader.local (incFNameLevel 1) $ NDefLetr f1 <$> annotateDef (h f1)

runAnnotate :: Exp Implicit Name a -> IO (AnnNExp a, OccMap)
runAnnotate e = do
  let r = annotate e
  ref <- newIORef emptyOccMap
  e' <- Reader.runReaderT r Conf{occMapRef = ref, vnameLevel = 0, fnameLevel = 0}
  occMap <- readIORef ref
  pure (e', occMap)

-- >>> let r = Op2 Cat r (Op0 Space)
-- >>> res <- runAnnotate r
-- >>> res
-- >>> introduceLets res
-- (AnnNExp @11 (NOp2 Cat (AnnNRef @11) (AnnNExp @12 (NOp0 Space))),fromList [(@12,1),(@11,2)])
-- NLetRec [NDefPair @11 (RecNExp (NOp2 Cat (RecNExp (NVar @11)) (RecNExp (NOp0 Space))))] (NVar @11)

-- >>> res <- runAnnotate $ let r = Op0 Space in Op2 Cat r r
-- >>> res
-- (AnnNExp @3 (NOp2 Cat (AnnNExp @4 (NOp0 Space)) (AnnNRef @4)),fromList [(@4,2),(@3,1)])

-- >>> res <- runAnnotate $ let r = Op0 Space in Lam $ \v -> UnUnit v $ Op2 Cat r r
-- >>> res
-- (AnnNExp @5 (NLam #0 (AnnNExp @6 (NUnUnit #0 (AnnNExp @7 (NOp2 Cat (AnnNExp @8 (NOp0 Space)) (AnnNRef @8)))))),fromList [(@5,1),(@7,1),(@6,1),(@8,2)])

data RecNExp a
  = RecNExp (NExpH RecNExp RecNDef a)
  | NLetRec [NDefPair] (NExpH RecNExp RecNDef a)
  deriving stock Show

newtype RecNDef as r
  = RecNDef (NDefH RecNExp RecNDef as r)
  deriving stock Show

data NDefPair where
  NDefPair :: FName a -> RecNExp a -> NDefPair

deriving stock instance Show NDefPair

splitDefs ::
  [NDefPair]
  -> (forall as. Env FName as -> Env RecNExp as -> r)
  -> r
splitDefs [] k = k ENil ENil
splitDefs (NDefPair x e : defs) k =
  splitDefs defs $ \xs es -> k (x :. xs) (e :. es)

type DefMap = H.HashMap SomeStableExpName SomeExp

data SomeExp where
  SomeExp :: RecNExp a -> SomeExp

lookupDefMap :: StableExpName a -> DefMap -> Maybe (RecNExp a)
lookupDefMap n m = case H.lookup (SomeStableExpName n) m of
  Just (SomeExp v) -> Just (unsafeCoerce v)
  Nothing -> Nothing

insertDefMap :: StableExpName a -> RecNExp a -> DefMap -> DefMap
insertDefMap n e = H.insert (SomeStableExpName n) (SomeExp e)

emptyDefMap :: DefMap
emptyDefMap = H.empty

instance Semigroup LMaps where
  LMaps{loccMap = o1, ldefMap = d1} <> LMaps{loccMap = o2, ldefMap = d2} =
    LMaps{loccMap = H.unionWith (+) o1 o2, ldefMap = H.union d1 d2}

instance Monoid LMaps where
  mempty = LMaps{loccMap = emptyOccMap, ldefMap = emptyDefMap}

data LMaps
  = LMaps
  { loccMap :: OccMap
  , ldefMap :: DefMap
  }

introduceLets ::
  (AnnNExp a, OccMap) -> RecNExp a
introduceLets (e, occMap) = fst $ Writer.runWriter (introLets occMap e)

introLets ::
  OccMap
  -> AnnNExp a
  -> Writer LMaps (RecNExp a)
introLets _occMap (AnnNRef sn) = do
  let key = SomeStableExpName sn
  Writer.tell LMaps{loccMap = insertOccMap key 1 emptyOccMap, ldefMap = emptyDefMap}
  pure $ RecNExp $ NVar (SName sn)
introLets occMap (AnnNExp sn e0) =
  let (e', LMaps{loccMap = counter, ldefMap = dMap}) = Writer.runWriter (go e0)
      key = SomeStableExpName sn
      -- Update `counter` first to include this occurrence of `sn`
      counter' = case lookupOccMap key counter of
        Just n -> insertOccMap key (succ n) counter
        _ -> insertOccMap key 1 counter
      -- Similarly, update `dMap` to include `sn` -> `e`
      dMap' = insertDefMap sn (RecNExp e') dMap
      -- `checkCnt k` tells if there is no occurrences of `k` upwards.
      checkCnt k =
        let cnt1 = fromMaybe 0 $ lookupOccMap k occMap
            cnt2 = fromMaybe 0 $ lookupOccMap k counter'
        in  cnt1 == cnt2 && cnt1 > 1
      -- Names to be defined here.
      defNames = [k | k <- H.keys counter', checkCnt k]
      defs = flip concatMap defNames $ \(SomeStableExpName x) -> case lookupDefMap x dMap' of
        Just e -> [NDefPair (SName x) e]
        _ -> error "introLets: cannot happen"
      e''
        | key `elem` defNames =
            -- Produce let x = e ... in x instead of let x = e ... in e
            NLetRec defs $ NVar (SName sn)
        | null defs = RecNExp e'
        | otherwise = NLetRec defs e'
      counter'' = foldr H.delete counter' defNames
  in  Writer.writer (e'', LMaps{loccMap = counter'', ldefMap = dMap'})
  where
    go :: NExpH AnnNExp AnnNDef a -> Writer LMaps (NExpH RecNExp RecNDef a)
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
    goBranch :: NBranch AnnNExp b a -> Writer LMaps (NBranch RecNExp b a)
    goBranch (NBranch pij b e) = NBranch pij b <$> introLets occMap e

-- goDef :: NDefH AnnNExp AnnNDef as r -> Writer LMaps (NDefH RecNExp RecNDef as r)
-- goDef (NDefRet e) = NDefRet <$> introLets occMap e
-- goDef (NDefCons e (AnnNDef d)) = NDefCons <$> introLets occMap e <*> (RecNDef <$> goDef d)
-- goDef (NDefLetr x (AnnNDef d)) = NDefLetr x . RecNDef <$> goDef d

data SomeVar v where
  SomeVar :: In v a -> SomeVar v

data SomeEExp v where
  SomeEExp :: Exp Explicit v a -> SomeEExp v

data SomeFName where
  SomeFName :: FName a -> SomeFName

instance Eq SomeFName where
  SomeFName fn == SomeFName fn' = fn == unsafeCoerce fn'

instance Hashable SomeFName where
  hashWithSalt salt (SomeFName n) =
    hashWithSalt @(Either Int SomeStableExpName) salt $
      case n of
        FName i -> Left i
        SName sn -> Right (SomeStableExpName sn)

type VMap v = H.HashMap Int (SomeVar v)
type FMap v = H.HashMap SomeFName (SomeEExp v)

insertVMap :: VName a -> In v a -> VMap v -> VMap v
insertVMap (VName i) x = H.insert i (SomeVar x)

lookupVMap :: VName a -> VMap v -> Maybe (In v a)
lookupVMap (VName i) vMap = case H.lookup i vMap of
  Just (SomeVar v) -> Just (unsafeCoerce v)
  Nothing -> Nothing

insertFMap :: FName a -> Exp Explicit v a -> FMap v -> FMap v
insertFMap fn f = H.insert (SomeFName fn) (SomeEExp f)

lookupFMap :: FName a -> FMap v -> Maybe (Exp Explicit v a)
lookupFMap fn fMap = case H.lookup (SomeFName fn) fMap of
  Just (SomeEExp e) -> Just (unsafeCoerce e)
  Nothing -> Nothing

type UnnameM v = Reader (VMap v, FMap v)

unname :: RecNExp a -> UnnameM v (Exp Explicit v a)
unname (RecNExp e) = unnameWork e
unname (NLetRec defs e) = Reader.reader $ \(vMap, fMap) ->
  splitDefs defs $ \xs es ->
    letrec
      xs
      ( \xxs ->
          let fMap' = extendMap xs xxs fMap
              es' = mapEnv (\ei -> Reader.runReader (unname ei) (vMap, fMap')) es
              e' = Reader.runReader (unnameWork e) (vMap, fMap')
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

unnameWork :: NExpH RecNExp RecNDef a -> UnnameM v (Exp Explicit v a)
unnameWork e0 = case e0 of
  NVar f -> do
    (_, fMap) <- Reader.ask
    case lookupFMap f fMap of
      Just v -> pure v
      Nothing -> error "unname: IMPOSSIBLE. Unreferenced variable."
  NLam x e -> do
    (vMap, fMap) <- Reader.ask
    pure $ Lam $ \xx ->
      let vMap' = insertVMap x xx vMap
      in  Reader.runReader (unname e) (vMap', fMap)
  NApp e x -> do
    xx <- resolveVar x
    App <$> unname e <*> pure xx
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
        _ -> error $ "unname: open expression detected. " ++ show e0
