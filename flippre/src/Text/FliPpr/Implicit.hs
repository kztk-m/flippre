{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Text.FliPpr.Implicit where

import Data.Kind (Type)
import Text.FliPpr.Internal.Core

-- import Control.Monad.Reader (ReaderT)
-- import qualified Control.Monad.Reader as Reader
-- import Data.IORef
-- import Data.Kind (Type)
-- import qualified Data.RangeSet.List as RS
-- import Data.Typeable
-- import System.Mem.StableName
-- import qualified Text.FliPpr.Grammar as G
-- import Text.FliPpr.Internal.Type (Branch (..), D, FType (..), PartialBij (..), type (~>))

-- import Data.Bits (xor)
-- import qualified Data.HashMap.Strict as H
-- import Data.Hashable (Hashable (..))

-- import Control.Arrow ((***))
-- import Data.Maybe (fromJust, fromMaybe)
-- import Debug.Trace (trace)
-- import qualified Unembedding as Un
-- import Unembedding.Env (Env (..), lookEnv, mapEnv)
-- import Unsafe.Coerce (unsafeCoerce)

-- data Op0 = Space | Spaces | Line | LineBreak | Line' | NESpaces' | Text !String deriving stock Show
-- data Op1 = Align | Group | Next !Int deriving stock Show
-- data Op2 = Cat | BChoice deriving stock Show

-- -- The laziness of the constructor arguments are intentional.
-- data ExpH k1 k2 exp v a where
--   Lam :: (k1 b) => (v a -> exp v b) -> ExpH k1 k2 exp v (a ~> b)
--   App :: (k2 a) => exp v (a ~> b) -> v a -> ExpH k1 k2 exp v b
--   Case :: v a -> [Branch v (exp v) a t] -> ExpH k1 k2 exp v t
--   UnPair :: v (a, b) -> (v a -> v b -> exp v t) -> ExpH k1 k2 exp v t
--   UnUnit :: v () -> exp v a -> ExpH k1 k2 exp v a
--   CharAs :: v Char -> RS.RSet Char -> ExpH k1 k2 exp v D
--   Abort :: ExpH k1 k2 exp v D
--   Op0 :: !Op0 -> ExpH k1 k2 exp v D
--   Op1 :: !Op1 -> exp v D -> ExpH k1 k2 exp v D
--   Op2 :: !Op2 -> exp v D -> exp v D -> ExpH k1 k2 exp v D

-- newtype Exp v a = Exp {unExp :: ExpH Typeable Typeable Exp v a}

-- type Ix = G.Ix

-- data DBranch e a as (t :: FType) where
--   DBranch :: (PartialBij a b) -> e (b : as) t -> DBranch e a as t

-- instance (forall env. Show (e env t)) => Show (DBranch e as a t) where
--   show (DBranch (PartialBij s _ _) e) = show (s, e)

-- data DExpH e as a where
--   DLam :: e (a : as) b -> DExpH e as (a ~> b)
--   DApp :: e as (a ~> b) -> Ix as a -> DExpH e as b
--   DCase :: Ix as a -> [DBranch e a as t] -> DExpH e as t
--   DUnPair :: Ix as (a, b) -> e (a : b : as) t -> DExpH e as t
--   DUnUnit :: Ix as () -> e as a -> DExpH e as a
--   DCharAs :: Ix as Char -> RS.RSet Char -> DExpH e as D
--   DAbort :: DExpH e as D
--   DOp0 :: !Op0 -> DExpH e as D
--   DOp1 :: !Op1 -> e as D -> DExpH e as D
--   DOp2 :: !Op2 -> e as D -> e as D -> DExpH e as D

-- deriving stock instance (forall env t. Show (e env t)) => Show (DExpH e as a)

-- data StableExpName a where
--   StableExpName ::
--     (Typeable a) => {getStableName :: StableName (Exp (Un.EnvI Ix) a)} -> StableExpName a

-- instance Show (StableExpName a) where
--   show (StableExpName sn) = "@" ++ show (hashStableName sn)

-- data Sn where
--   Sn :: (Typeable a) => StableName (Exp (Un.EnvI Ix) a) -> Sn

-- instance Show Sn where
--   show (Sn x) = "@" ++ show (hashStableName x)

-- instance Eq Sn where
--   Sn x1 == Sn x2 =
--     case gcast x2 of
--       Nothing -> False
--       Just x2' -> x1 == x2'

-- instance Hashable Sn where
--   hashWithSalt salt (Sn x) = salt `xor` hashStableName x

-- type RefNumber = Int

-- data AnnDExp as a = AnnDExp (StableExpName a) (DExpH AnnDExp as a) | AnnRef (StableExpName a)
--   deriving stock Show

-- type Memo = H.HashMap Sn Int

-- newtype Refs = Refs
--   { memoRef :: IORef Memo
--   }

-- lookupMemo :: Sn -> Memo -> Maybe Int
-- lookupMemo = H.lookup

-- insertMemo :: Sn -> Int -> Memo -> Memo
-- insertMemo = H.insert

-- modifyMemo :: Sn -> (Int -> Int) -> Memo -> Memo
-- modifyMemo = flip H.adjust

-- emptyMemo :: Memo
-- emptyMemo = H.empty

-- unionMemo :: Memo -> Memo -> Memo
-- unionMemo = H.unionWith (+)

-- newtype AnnSem as a = AnnSem {runAnnSem :: ReaderT Refs IO (AnnDExp as a)}
-- newtype AnnBranchSem a as t = AnnBranchSem {runAnnBranchSem :: ReaderT Refs IO (DBranch AnnDExp a as t)}

-- newtype AnnBranchesSem a as t = AnnBranchesSem {runAnnBranchesSem :: ReaderT Refs IO [DBranch AnnDExp a as t]}

-- -- type Sem = Un.EnvI

-- runAnnotate :: (Typeable a) => Exp (Un.EnvI Ix) a -> IO (AnnDExp '[] a, Memo)
-- runAnnotate e = do
--   let r = runAnnSem (Un.runClose (annotate e))
--   mref <- newIORef emptyMemo
--   res <- Reader.runReaderT r Refs{memoRef = mref}
--   memo <- readIORef mref
--   pure (res, memo)

-- annotate :: forall a. (Typeable a) => Exp (Un.EnvI Ix) a -> Un.EnvI AnnSem a
-- annotate !e = Un.EnvI $ \sh -> AnnSem $ do
--   refs <- Reader.ask
--   sn <- Reader.lift $ makeStableName e
--   let key = Sn sn
--   -- Reader.lift $ print (hashStableName sn)
--   memo <- Reader.lift $ readIORef (memoRef refs)
--   -- Reader.lift $ print memo
--   case lookupMemo key memo of
--     Just _ -> do
--       Reader.lift $ modifyIORef' (memoRef refs) $ modifyMemo key succ
--       pure $ AnnRef (StableExpName sn)
--     Nothing -> do
--       Reader.lift $ modifyIORef' (memoRef refs) $ insertMemo key 1
--       let wrap :: forall as0. ReaderT Refs IO (DExpH AnnDExp as0 a) -> AnnSem as0 a
--           wrap = AnnSem . fmap (AnnDExp (StableExpName sn))
--       runAnnSem $ flip Un.runEnvI sh $ case unExp e of
--         Abort ->
--           Un.liftFO0 $ wrap (pure DAbort)
--         Op0 op ->
--           Un.liftFO0 $ wrap (pure $ DOp0 op)
--         Op1 op e1 ->
--           Un.liftFO1 (\r1 -> wrap $ DOp1 op <$> runAnnSem r1) (annotate e1)
--         Op2 op e1 e2 ->
--           Un.liftFO2
--             (\r1 r2 -> wrap $ DOp2 op <$> runAnnSem r1 <*> runAnnSem r2)
--             (annotate e1)
--             (annotate e2)
--         Lam h ->
--           let h' = Un.liftSOn' @Ix @AnnSem (Un.ol1 :. ENil) Proxy $ \r ->
--                 wrap $ DLam <$> runAnnSem r
--           in  h' (annotate . h)
--         App e1 x1 ->
--           Un.liftFO2' (\r1 r2 -> wrap $ DApp <$> runAnnSem r1 <*> pure r2) (annotate e1) x1
--         UnPair x1 h ->
--           let h' = Un.liftSOn' @Ix @AnnSem (Un.ol0 :. Un.ol2 :. ENil) Proxy $ \r1 r2 ->
--                 wrap $ DUnPair r1 <$> runAnnSem r2
--           in  h' x1 (\x y -> annotate (h x y))
--         UnUnit x e1 -> Un.liftFO2' (\r1 r2 -> wrap $ DUnUnit r1 <$> runAnnSem r2) x (annotate e1)
--         CharAs x1 cs ->
--           Un.liftFO1' (\r1 -> wrap $ pure $ DCharAs r1 cs) x1
--         Case x bs ->
--           Un.liftFO2' (\x1 rbs -> wrap $ DCase x1 <$> runAnnBranchesSem rbs) x (annotateBranches bs)

-- annotateBranches ::
--   (Typeable t) =>
--   [Branch (Un.EnvI Ix) (Exp (Un.EnvI Ix)) a t]
--   -> Un.EnvI (AnnBranchesSem a) t
-- annotateBranches =
--   foldr cons nil
--   where
--     cons =
--       Un.liftFO2'
--         ( \r rs ->
--             AnnBranchesSem $
--               (:) <$> runAnnBranchSem r <*> runAnnBranchesSem rs
--         )
--         . annotateBranch
--     nil = Un.liftFO0 $ AnnBranchesSem $ pure []

-- annotateBranch :: forall a t. (Typeable t) => Branch (Un.EnvI Ix) (Exp (Un.EnvI Ix)) a t -> Un.EnvI (AnnBranchSem a) t
-- annotateBranch (Branch pij h) =
--   let h' = Un.liftSOn' @Ix @(AnnBranchSem a) (Un.ol1 :. ENil) Proxy $ \r ->
--         AnnBranchSem $ DBranch pij <$> runAnnSem r
--   in  h' (annotate . h)

-- -- >>> let r = Op2 Cat r (Op0 Space)
-- -- >>> res <- runAnnotate r
-- -- >>> res
-- -- >>> toNameTerm res
-- -- (AnnDExp @15 (DOp2 Cat (AnnRef @15) (AnnDExp @14 (DOp0 Space))),fromList [(@15,2),(@14,1)])
-- -- NLetRec [NDefPair @15 (NOp2 Cat (NVar @15) (NLetRec [] (NOp0 Space)))] (NVar @15)

-- -- >>> let r = Op2 Cat r r
-- -- >>> res <- runAnnotate r
-- -- >>> res
-- -- >>> toNameTerm res
-- -- (AnnDExp @12 (DOp2 Cat (AnnRef @12) (AnnRef @12)),fromList [(@12,3)])
-- -- NLetRec [NDefPair @12 (NOp2 Cat (NVar @12) (NVar @12))] (NVar @12)

-- -- >>> res <- runAnnotate $ let r = Op0 Space in Op2 Cat r r
-- -- >>> res
-- -- >>> toNameTerm res
-- -- (AnnDExp @11 (DOp2 Cat (AnnDExp @3 (DOp0 Space)) (AnnRef @3)),fromList [(@3,2),(@11,1)])
-- -- NLetRec [NDefPair @3 (NOp0 Space)] (NOp2 Cat (NOp0 Space) (NVar @3))

-- -- >>> res <- runAnnotate $ let r = Op0 Space in Lam $ \v -> UnUnit v $ Op2 Cat r r
-- -- >>> res
-- -- >>> toNameTerm res
-- -- (AnnDExp @24 (DLam (AnnDExp @23 (DUnUnit IxZ (AnnDExp @22 (DOp2 Cat (AnnDExp @21 (DOp0 Space)) (AnnRef @21)))))),fromList [(@21,2),(@23,1),(@22,1),(@24,1)])
-- -- NLam #0 (NUnUnit #0 (NLetRec [NDefPair @21 (NOp0 Space)] (NOp2 Cat (NOp0 Space) (NVar @21))))

-- -- >>> res <- runAnnotate $ let r = Lam $ \v -> UnUnit v $ Op2 Cat (App r v) (Op0 Space) in r
-- -- >>> res
-- -- >>> toNameTerm res
-- -- (AnnDExp @15 (DLam (AnnDExp @14 (DUnUnit IxZ (AnnDExp @12 (DOp2 Cat (AnnDExp @11 (DApp (AnnRef @15) IxZ)) (AnnDExp @3 (DOp0 Space))))))),fromList [(@3,1),(@12,1),(@15,2),(@14,1),(@11,1)])
-- -- NLetRec [NDefPair @15 (NLam #0 (NUnUnit #0 (NOp2 Cat (NApp (NVar @15) #0) (NOp0 Space))))] (NVar @15)

-- data NBranch ename name a t where
--   NBranch :: PartialBij a b -> name b -> NExp ename name t -> NBranch ename name a t

-- instance
--   (forall x. Show (ename x), forall x. Show (name x)) =>
--   Show (NBranch ename name a t)
--   where
--   show (NBranch (PartialBij s _ _) n e) = show (s, n, e)

-- -- | Named representation of terms
-- data NExp ename name a where
--   NLam :: name a -> NExp ename name b -> NExp ename name (a ~> b)
--   NApp :: NExp ename name (a ~> b) -> name a -> NExp ename name b
--   NCase :: name a -> [NBranch ename name a t] -> NExp ename name t
--   NUnPair :: name (a, b) -> name a -> name b -> NExp ename name t -> NExp ename name t
--   NUnUnit :: name () -> NExp ename name t -> NExp ename name t
--   NCharAs :: name Char -> RS.RSet Char -> NExp ename name D
--   NAbort :: NExp ename name D
--   NOp0 :: !Op0 -> NExp ename name D
--   NOp1 :: !Op1 -> NExp ename name D -> NExp ename name D
--   NOp2 :: !Op2 -> NExp ename name D -> NExp ename name D -> NExp ename name D
--   NVar :: ename a -> NExp ename name a
--   NLetRec :: [DefPair ename name] -> NExp ename name b -> NExp ename name b

-- deriving stock instance
--   (forall x. Show (ename x), forall x. Show (name x)) =>
--   Show (NExp ename name a)

-- data DefPair ename name where
--   NDefPair :: ename a -> NExp ename name a -> DefPair ename name

-- splitDefs ::
--   [DefPair ename name]
--   -> (forall as. Env ename as -> Env (NExp ename name) as -> r)
--   -> r
-- splitDefs [] k = k ENil ENil
-- splitDefs (NDefPair x e : defs) k =
--   splitDefs defs $ \xs es -> k (x :. xs) (e :. es)

-- deriving stock instance
--   (forall x. Show (ename x), forall x. Show (name x)) =>
--   Show (DefPair ename name)

-- data NExpOfSomeType ename name where
--   ExistType :: (Typeable a) => NExp ename name a -> NExpOfSomeType ename name

-- type BodyMap name = H.HashMap Sn (NExpOfSomeType StableExpName name)

-- newtype IxName a = IxName Int

-- instance Show (IxName a) where
--   show (IxName n) = "#" ++ show n

-- toNameTerm :: (AnnDExp '[] a, Memo) -> NExp StableExpName IxName a
-- toNameTerm (ae, memo) =
--   let (ne, _, _) = nameTerm memo ae ENil 0
--   in  ne

-- nameTerm ::
--   forall a as.
--   Memo
--   -> AnnDExp as a
--   -> Env IxName as
--   -> Int
--   -> (NExp StableExpName IxName a, BodyMap IxName, Memo)
-- nameTerm _memo (AnnRef sn@(StableExpName _)) _names _lenNames =
--   (NVar sn, H.empty, insertMemo (Sn $ getStableName sn) 1 emptyMemo)
-- nameTerm memo (AnnDExp sn@(StableExpName _) e) names lenNames =
--   let (ne, bmap, counter) = go e
--       counter' = case lookupMemo key counter of
--         Just n -> insertMemo key (succ n) counter
--         _ -> insertMemo key 1 counter
--       keys = H.keys counter'
--       checkCnt k =
--         let cnt1 = fromMaybe 0 $ lookupMemo k memo
--             cnt2 = fromMaybe 0 $ lookupMemo k counter'
--         in  cnt1 == cnt2 && cnt1 > 1
--       keys' = [k | k <- keys, checkCnt k]
--       ne' = if key `elem` keys' then NVar sn else ne
--       bmap' = H.insert key (ExistType ne) bmap
--       defs = flip concatMap keys' $ \k@(Sn t) ->
--         case H.lookup k bmap' of
--           Just (ExistType ebody0)
--             | Just ebody <- gcast ebody0 ->
--                 [NDefPair (StableExpName t) ebody]
--           _ -> error "nameTerm: cannot happen."
--       counter'' = foldr H.delete counter' keys'
--       ne'' = if null defs then ne' else NLetRec defs ne'
--   in  trace (show key ++ " -> " ++ show counter') $ (ne'', bmap', counter'')
--   where
--     key = Sn (getStableName sn)

--     go :: DExpH AnnDExp as a -> (NExp StableExpName IxName a, BodyMap IxName, Memo)
--     go (DLam ae) =
--       let newName = IxName lenNames
--           (ne, bmap, counter) = nameTerm memo ae (newName :. names) (succ lenNames)
--       in  (NLam newName ne, bmap, counter)
--     go (DApp ae ix) =
--       let (ne, bmap, counter) = nameTerm memo ae names lenNames
--       in  (NApp ne (lookEnv names ix), bmap, counter)
--     go (DUnPair ix ae) =
--       let nn1 = IxName lenNames
--           nn2 = IxName (lenNames + 1)
--           (ne, bmap, counter) = nameTerm memo ae (nn1 :. nn2 :. names) (lenNames + 2)
--       in  (NUnPair (lookEnv names ix) nn1 nn2 ne, bmap, counter)
--     go (DUnUnit ix ae) =
--       let (ne, bmap, counter) = nameTerm memo ae names lenNames
--       in  (NUnUnit (lookEnv names ix) ne, bmap, counter)
--     go (DCharAs ix rs) = (NCharAs (lookEnv names ix) rs, H.empty, emptyMemo)
--     go DAbort = (NAbort, H.empty, emptyMemo)
--     go (DOp0 op) = (NOp0 op, H.empty, emptyMemo)
--     go (DOp1 op ae) =
--       let (ne, bmap, counter) = nameTerm memo ae names lenNames
--       in  (NOp1 op ne, bmap, counter)
--     go (DOp2 op ae1 ae2) =
--       let (ne1, bmap1, counter1) = nameTerm memo ae1 names lenNames
--           (ne2, bmap2, counter2) = nameTerm memo ae2 names lenNames
--       in  (NOp2 op ne1 ne2, H.union bmap1 bmap2, unionMemo counter1 counter2)
--     go (DCase ix brs) =
--       let (nbrs, bmap, counter) = goBranches brs
--       in  (NCase (lookEnv names ix) nbrs, bmap, counter)

--     goBranches :: [DBranch AnnDExp b as a] -> ([NBranch StableExpName IxName b a], BodyMap IxName, Memo)
--     goBranches [] = ([], H.empty, emptyMemo)
--     goBranches (br : brs) =
--       let (br', bmap1, counter1) = goBranch br
--           (brs', bmap2, counter2) = goBranches brs
--       in  (br' : brs', H.union bmap1 bmap2, unionMemo counter1 counter2)

--     goBranch :: DBranch AnnDExp b as a -> (NBranch StableExpName IxName b a, BodyMap IxName, Memo)
--     goBranch (DBranch pij ae) =
--       let nn = IxName lenNames
--           (ne, bmap, counter) = nameTerm memo ae (nn :. names) (lenNames + 1)
--       in  (NBranch pij nn ne, bmap, counter)

-- type family FName (v :: Type -> Type) :: FType -> Type

-- class NoConstraint (a :: k)
-- instance NoConstraint a

-- data CoreExp v a
--   = CVar (FName v a)
--   | CLocal (CoreDef v '[] a)
--   | CExp (ExpH NoConstraint NoConstraint CoreExp v a)

-- data CoreDef v as r where
--   CoreRet :: CoreExp v r -> CoreDef v '[] r
--   CoreCons :: CoreExp v a -> CoreDef v as r -> CoreDef v (a : as) r
--   CoreLetr :: (FName v a -> CoreDef v (a : as) r) -> CoreDef v as r

-- instance G.Defs (CoreExp v) where
--   newtype D (CoreExp v) as r = DCoreExp {unDCoreExp :: CoreDef v as r}
--   liftD = DCoreExp . CoreRet
--   consD e (DCoreExp ds) = DCoreExp $ CoreCons e ds
--   unliftD (DCoreExp ds) = CLocal ds
--   letrD h = DCoreExp $ CoreLetr (unDCoreExp . h . CVar)

-- letrec :: (G.Defs f) => Env proxy as -> (Env f as -> (Env f as, f r)) -> f r
-- letrec sh h = G.local $ letrecM sh (pure . h)

-- letrecM :: (G.Defs f) => Env proxy as -> (Env f as -> G.DefM f (Env f as, res)) -> G.DefM f res
-- letrecM ENil h = snd <$> h ENil
-- letrecM (ECons _ sh) h =
--   G.letr1 $ \x -> letrecM sh $ \xs -> do
--     (vvs, r) <- h (ECons x xs)
--     case vvs of
--       ECons v vs -> pure (vs, (v, r))

-- data SomeIxName where
--   SomeIxName :: IxName a -> SomeIxName

-- instance Eq SomeIxName where
--   (SomeIxName (IxName n)) == (SomeIxName (IxName m)) = n == m
-- instance Hashable SomeIxName where
--   hashWithSalt salt (SomeIxName (IxName n)) = salt `xor` n

-- data SomeIVar v where
--   SomeIVar :: v a -> SomeIVar v

-- type IxMap v = H.HashMap SomeIxName (SomeIVar v)

-- data SomeCoreExp v where
--   SomeCoreExp :: (Typeable a) => CoreExp v a -> SomeCoreExp v

-- type SnMap v = H.HashMap Sn (SomeCoreExp v)

-- lookupSnMap :: StableExpName a -> SnMap v -> Maybe (CoreExp v a)
-- lookupSnMap (StableExpName k) oMap =
--   case H.lookup (Sn k) oMap of
--     Just (SomeCoreExp res) -> gcast res
--     Nothing -> Nothing

-- insertSnMap :: StableExpName a -> CoreExp v a -> SnMap v -> SnMap v
-- insertSnMap (StableExpName n) e = H.insert (Sn n) (SomeCoreExp e)

-- lookupIxMap :: IxName a -> IxMap v -> Maybe (v a)
-- lookupIxMap n iMap =
--   case H.lookup (SomeIxName n) iMap of
--     Just (SomeIVar x) -> Just $ unsafeCoerce x
--     Nothing -> Nothing

-- insertIxMap :: IxName a -> v a -> IxMap v -> IxMap v
-- insertIxMap n x = H.insert (SomeIxName n) (SomeIVar x)

-- unname :: forall a v. NExp StableExpName IxName a -> IxMap v -> SnMap v -> CoreExp v a
-- unname e0 iMap oMap = case e0 of
--   NVar f -> lookupSnMap' f
--   NLam x e -> CExp (Lam $ \xx -> unname e (insertIxMap x xx iMap) oMap)
--   NApp e1 e2 -> CExp $ App (unname e1 iMap oMap) (lookupIxMap' e2)
--   NUnPair x x1 x2 e -> CExp $ UnPair (lookupIxMap' x) $ \xx1 xx2 ->
--     unname e (insertIxMap x1 xx1 $ insertIxMap x2 xx2 iMap) oMap
--   NUnUnit x e -> CExp $ UnUnit (lookupIxMap' x) (unname e iMap oMap)
--   NCharAs x s -> CExp $ CharAs (lookupIxMap' x) s
--   NCase x brs -> CExp $
--     Case (lookupIxMap' x) $
--       flip map brs $
--         \(NBranch pij y e) ->
--           Branch pij (\yy -> unname e (insertIxMap y yy iMap) oMap)
--   NAbort -> CExp Abort
--   NOp0 op -> CExp (Op0 op)
--   NOp1 op e -> CExp $ Op1 op (unname e iMap oMap)
--   NOp2 op e1 e2 -> CExp $ Op2 op (unname e1 iMap oMap) (unname e2 iMap oMap)
--   NLetRec ds e -> splitDefs ds $ \xs es ->
--     letrec
--       xs
--       ( \xxs ->
--           let oMap' = extendMap xs xxs oMap
--           in  (Unembedding.Env.mapEnv (\y -> unname y iMap oMap') es, unname e iMap oMap')
--       )
--       -- let go [] im =
--       -- G.local $ go ds iMap
--   where
--     extendMap :: Env StableExpName as -> Env (CoreExp v) as -> SnMap v -> SnMap v
--     extendMap ENil ENil m = m
--     extendMap (x :. xs) (e :. es) m = extendMap xs es (insertSnMap x e m)

--     lookupSnMap' :: StableExpName x -> CoreExp v x
--     lookupSnMap' x = case lookupSnMap x oMap of
--       Just r -> r
--       Nothing -> error "unname: IMPOSSIBLE: Unreferenced variable found."

--     lookupIxMap' :: IxName x -> v x
--     lookupIxMap' x = case lookupIxMap x iMap of
--       Just r -> r
--       Nothing -> error $ "unname: open expression detected." ++ show e0

class Memoizable a where
  -- | *First-order* (non-function) datatype to store each computation result
  data Store a :: Type

  toStore :: a -> Store a
  fromStore :: Store a -> a

instance Memoizable (Exp s v t) where
  newtype Store (Exp s v t) = ExpStore (Exp s v t)
  toStore = ExpStore
  fromStore (ExpStore s) = s

instance (Memoizable a, Memoizable b) => Memoizable (a, b) where
  newtype Store (a, b) = Tuple2Store (Store a, Store b)
  toStore (a, b) = Tuple2Store (toStore a, toStore b)
  fromStore (Tuple2Store ~(a, b)) = (fromStore a, fromStore b)

instance (Memoizable a) => Memoizable (Bool -> a) where
  newtype Store (Bool -> a) = BoolStore (Store a, Store a)

  toStore f = BoolStore (toStore $ f True, toStore $ f False)
  fromStore (BoolStore ~(t, f)) b = if b then fromStore t else fromStore f
