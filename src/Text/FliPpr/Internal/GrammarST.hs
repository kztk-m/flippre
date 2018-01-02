{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE RecursiveDo #-}
module Text.FliPpr.Internal.GrammarST (
  module Text.FliPpr.Internal.GrammarST.Core,
  inline, removeNonProductive, fuseWithTransducer, optSpaces, foldGrammar
  )
  where

import Control.Monad.Reader

-- import Control.Monad.Fix

import Control.Applicative as A (Alternative(..), Const(..)) 

import Data.Typeable ((:~:)(..))

import Data.Coerce 

import Data.Map2 (Ord2(..), Ordering2(..), Map2) 
import qualified Data.Map2 as M2 

import Data.List (sortBy)

-- import qualified Data.IntSet as IS 

-- import Debug.Trace


import Text.FliPpr.Internal.GrammarST.Core 
import Text.FliPpr.Internal.Ref

data TT s c m res = TT (forall a. RHS s c a -> m (res s c a))
                       (forall a. Prod s c a -> m (res s c a))
                       (forall a. Symb RHS s c a -> m (res s c a))

{-
The definition only corresponds to single fold. 
-}
foldGrammar ::
  forall s c res m. (MonadRef s m, MonadFix m) => 
  (forall a. m (res s c a)) ->
  (forall a. res s c a -> res s c a -> m (res s c a)) -> 
  (forall a. Maybe (a :~: ()) -> res s c a -> m (res s c a)) -> 
  (forall a. a -> m (res s c a)) ->
  (forall a b. res s c a -> res s c (a -> b) -> m (res s c b)) ->
  (c -> m (res s c c)) ->
  (forall a. Ref s (RHS s c a) -> res s c a -> m (res s c a)) -> TT s c m res 
  -- forall a. Grammar c a -> RefM s (rhs s c a)
foldGrammar rhsNil rhsCons rhsCheckVoid prodNil prodCons term nt =
  TT (\rhs  -> run (procRHS rhs))
     (\prod -> run (procProd prod))
     (\symb -> run (procSymb symb))
  where
    run :: ReaderT (Ref s (Map2 (RefK s (RHS s c)) (res s c))) m d -> m d 
    run x = do
      tbRef <- newRef M2.empty
      runReaderT x tbRef 
    
    procRHS :: forall a. RHS s c a -> ReaderT (Ref s (Map2 (RefK s (RHS s c)) (res s c))) m (res s c a)
    procRHS (RHS rs b) = lift . rhsCheckVoid b =<< go rs
      where
        go [] = lift rhsNil
        go (x:xs) = do
          x'  <- procProd x
          xs' <- go xs
          lift $ rhsCons x' xs' 

    procProd :: forall a. Prod s c a -> ReaderT (Ref s (Map2 (RefK s (RHS s c)) (res s c))) m (res s c a)
    procProd (PNil f)    = lift $ prodNil f
    procProd (PCons s r) = do
      s' <- procSymb s
      r' <- procProd r
      lift $ prodCons s' r'

    procSymb :: forall a. Symb RHS s c a -> ReaderT (Ref s (Map2 (RefK s (RHS s c)) (res s c))) m (res s c a)
    procSymb (Term c) = lift $ term c
    procSymb (NT x) = do
      tbRef <- ask
      tb <- lift $ readRef tbRef
      case M2.lookup (coerce x) tb of
        Just v  -> return v
        Nothing -> do
          rec g <- do
                lift $ writeRef tbRef (M2.insert (coerce x) g tb)
                rhs  <- lift $ readRef x 
                rhs' <- procRHS rhs
                lift $ nt x rhs' 
          return g
                
          
      




type TransM s c = ReaderT (Ref s (Map2 (RefK s (RHS s c)) (OpenGrammar s c))) (RefM s) 

inline :: Grammar c a -> Grammar c a
inline (Grammar m) = finalize $ do
  ref <- m 
  tbRef  <- newRef M2.empty
  runReaderT (inlineSymb (NT ref)) tbRef
  where
    getTable :: TransM s c (Map2 (RefK s (RHS s c)) (OpenGrammar s c))
    getTable = do
      tbRef <- ask
      lift $ readRef tbRef

    modifyTable f = do
      tbRef <- ask
      tb <- lift $ readRef tbRef
      lift $ writeRef tbRef (f tb) 
    
    inlineRHS :: RHS s c a -> TransM s c (OpenGrammar s c a) 
    inlineRHS (RHS rs Nothing)     = foldr (<|>) A.empty <$> mapM inlineProd rs
    inlineRHS (RHS rs (Just Refl)) = (discard . foldr (<|>) A.empty <$> mapM inlineProd rs)

    inlineProd :: Prod s c a -> TransM s c (OpenGrammar s c a)
    inlineProd (PNil f)    = return $ pure f
    inlineProd (PCons s r) = liftM2 (<*>) (fmap (\a k -> k a) <$> inlineSymb s) (inlineProd r)

    inlineSymb :: Symb RHS s c a -> TransM s c (OpenGrammar s c a)
    inlineSymb (Term c) = return $ term c
    inlineSymb (NT x) = do
      tb <- getTable
      case M2.lookup (coerce x) tb of
        Nothing -> do 
          modifyTable (M2.insert (coerce x) A.empty)
          rhs <- lift $ readRef x
          rec y  <- lift $ newRef (LazyRHS $ runOpenG g)
              let res = if inlinable rhs then g else OpenG $ return $ RSingle (PSymb (NT y))
              g  <- do
                modifyTable (M2.insert (coerce x) res)
                inlineRHS rhs 
          return res 
        Just res ->
          return res 

    -- it is intentional to check based on the previous grammar, as
    -- inspecting a grammar being constructed could result in a infinite loop, in this construction. 
    inlinable :: RHS s c a -> Bool
    inlinable (RHS rs _) = length rs <= 1 

-- newtype BoolR s c a = BoolR Bool

-- showPM :: Ord2 k1 =>
--           (forall a. k1 a -> String) ->
--           (forall a. k2 a -> String) ->
--           Map2 k1 k2 -> String 
-- showPM showKey showVal m = go (M2.toList m)
--   where
--     go [] = ""
--     go (M2.Entry k v:es) =
--       showKey k ++ " = " ++ showVal v ++ "\n" ++ go es 


-- -- Table to check whether a nonterminal is visited or not 
-- type VTable s c = Map2 (RefK s (RHS s c)) (Const ())

-- Table to store whether a nonterminal is productive or not 
type PTable s c = Map2 (RefK s (RHS s c)) (Const Bool)

-- Monad to remove non-productive rules 
type RemM s c = ReaderT (PTable s c, Ref s (Map2 (RefK s (RHS s c)) (OpenGrammar s c))) (RefM s)

data SomeRef s c = forall a. SomeRef (Ref s (RHS s c a))

removeNonProductive :: Grammar c a -> Grammar c a
removeNonProductive (Grammar m) = finalize $ do
  ref <- m 
  pmRef <- newRef M2.empty
  pm <- check pmRef ref
  rmRef <- newRef M2.empty 
  runReaderT (removeSymb (NT ref)) (pm, rmRef)
  where
    check pmRef ref = do
      ws <- gatherWorkList ref
      loop pmRef ws

    loop pmRef ws = do 
      pm <- readRef pmRef
      mapM_ (\(SomeRef ref) -> checkRef pmRef ref) ws
      pm' <- readRef pmRef
      if eqMap pm pm' then return pm else loop pmRef ws
        where
          eqMap pm pm' = go (M2.toList pm) (M2.toList pm')
            where
              go :: (Ord2 k, Eq b) => [M2.Entry k (Const b)] -> [M2.Entry k (Const b)] -> Bool 
              go []   []    = True
              go (M2.Entry k1 (Const b1):es1) (M2.Entry k2 (Const b2):es2) =
                case M2.compare2 k1 k2 of
                  EQ2 -> (b1 == b2) && go es1 es2
                  _   -> False 
              go _ _ = False

    gatherWorkList :: Ref s (RHS s c a) -> RefM s [SomeRef s c]
    gatherWorkList ref = do
      vmRef <- newRef M2.empty
      list <- runReaderT (goSymb (NT ref)) vmRef
      return $ nubWS list 
        where
          nubWS :: [SomeRef s c] -> [SomeRef s c]
          nubWS list = let m = foldr (\(SomeRef r) -> M2.insert (RefK r) (Const ())) M2.empty list
                           l = M2.toList m
                       in map (\(M2.Entry (RefK k) _) -> SomeRef k) l 
          
          goSymb :: Symb RHS s c a -> ReaderT (Ref s (Map2 (RefK s (RHS s c)) (Const ()))) (RefM s) [SomeRef s c]
          goSymb (Term _) = return []
          goSymb (NT ref) = do
            vmRef <- ask
            vm <- readRef vmRef
            case M2.lookup (coerce ref) vm of
              Just _  -> return []
              Nothing -> do
                modifyRef vmRef (M2.insert (coerce ref) (Const ()))
                rs <- readRef ref >>= goRHS
                return $ SomeRef ref:rs

          goRHS (RHS rs _) = concat <$> mapM goProd rs

          goProd :: Prod s c a -> ReaderT (Ref s (Map2 (RefK s (RHS s c)) (Const ()))) (RefM s) [SomeRef s c]
          goProd (PNil _) = return []
          goProd (PCons s r) =
            liftM2 (++) (goSymb s) (goProd r) 

    checkRef :: Ref s (PTable s c) -> Ref s (RHS s c a) -> RefM s ()
    checkRef pmRef ref = do
      pm <- readRef pmRef
      case M2.lookup (coerce ref) pm of
        Just (Const True) -> return () 
        _ -> do 
          rhs <- readRef ref
          let b = checkRHS pm rhs
          modifyRef pmRef (M2.insert (coerce ref) (Const b))
        where
          checkRHS pm (RHS rs _) = or $ map (checkProd pm) rs

          checkProd :: PTable s c -> Prod s c a -> Bool
          checkProd _  (PNil _)    = True
          checkProd pm (PCons s r) = checkSymb pm s && checkProd pm r

          checkSymb :: PTable s c -> Symb RHS s c a -> Bool
          checkSymb _  (Term _) = True
          checkSymb pm (NT x)   =
            case M2.lookup (coerce x) pm of
              Just (Const True) -> True
              _                 -> False 
                        
    removeRHS :: RHS s c a -> RemM s c (OpenGrammar s c a)
    removeRHS (RHS rs b) =
      tryDiscard b . unions <$> mapM removeProd rs

    removeProd :: Prod s c a -> RemM s c (OpenGrammar s c a)
    removeProd (PNil f) = return $ pure f
    removeProd (PCons s r) = do
      s' <- removeSymb s
      r' <- removeProd r
      return $ fmap (\a k -> k a) s' <*> r' 


    removeSymb :: Symb RHS s c a -> RemM s c (OpenGrammar s c a)
    removeSymb (Term c) = return $ term c
    removeSymb (NT x) = do
      (pm, rmRef) <- ask
      rm <- readRef rmRef 
      case M2.lookup (coerce x) pm of
        Just (Const True) ->
          case M2.lookup (coerce x) rm of
            Just res -> return res
            Nothing -> do
              rec res <- do
                    writeRef rmRef $ M2.insert (coerce x) res rm
                    rhs <- readRef x
                    g <- removeRHS rhs
                    y <- newRef $ LazyRHS $ runOpenG g
                    return $ OpenG $ return $ RSingle (PSymb (NT y))
              return res
        _ ->
          return A.empty 
                     
    

type Q = Int
data Transducer inc outc =
  Transducer Q                     -- ^ init state
             [Q]                   -- ^ all the states
             [Q]                   -- ^ final states
             (Trans inc outc)

data Trans inc outc = Trans (Q -> inc -> ([outc], Q)) -- ^ transitions
                            (Q -> Maybe [outc])             -- ^ final rules 

finalProd :: Q -> Trans inc outc -> Maybe [outc]
finalProd q (Trans _ f) = f q 


transTo :: Q -> inc -> Trans inc outc -> ([outc], Q)
transTo qi c (Trans tr _) = tr qi c 

data RefTuple s c q a = RefTuple (Ref s (RHS s c a)) q

instance Ord q => M2.Eq2 (RefTuple s c q)
instance Ord q => Ord2 (RefTuple s c q) where
  compare2 (RefTuple ref1 q1) (RefTuple ref2 q2) =
    case compare2 ref1 ref2 of
      LT2 -> LT2
      GT2 -> GT2
      EQ2 ->
        case compare q1 q2 of
          LT -> LT2
          GT -> GT2
          EQ -> EQ2 

type FuseM s inc outc = ReaderT (Ref s (Map2 (RefTuple s inc (Q,Q)) (OpenGrammar s outc))) (RefM s) 

tryDiscard :: forall a s c. Maybe (a :~: ()) -> OpenGrammar s c a -> OpenGrammar s c a
tryDiscard Nothing g     = g
tryDiscard (Just Refl) g = discard g 

unions :: forall f a. Alternative f => [f a] -> f a 
unions = foldr (<|>) A.empty 

fuseWithTransducer :: forall inc outc a. Grammar inc a -> Transducer inc outc -> Grammar outc a
fuseWithTransducer (Grammar m) (Transducer q0 qs qf tr) = finalize $ do
  ref <- m 
  tMap <- newRef $ M2.empty
  runReaderT
    (foldr (<|>) A.empty <$>
     mapM (\q1 -> do
              g <- goRef q0 q1 ref
              let Just os = finalProd q1 tr 
              return $ g <* fromList os) qf)
    tMap
  where
    fromList :: [outc] -> OpenGrammar s outc [outc]
    fromList []     = pure []
    fromList (o:os) = (:) <$> term o <*> fromList os 

    goRHS :: forall s a. Q -> Q -> RHS s inc a -> FuseM s inc outc (OpenGrammar s outc a)
    goRHS q q' (RHS rs b) = tryDiscard b . unions <$> mapM (\p -> goProd q q' p) rs

    goProd :: forall s a. Q -> Q -> Prod s inc a -> FuseM s inc outc (OpenGrammar s outc a)
    goProd q q' (PNil f) = return $ if q == q' then pure f else A.empty
    goProd q q' (PCons (Term c) r) = do 
      let (os, q0) = transTo q c tr
      g <- goProd q0 q' r 
      return $ fmap (\_ k -> k c) (fromList os) <*> g
    goProd q q' (PCons (NT x) r) =
      unions <$> 
      mapM (\qm -> do
               g1 <- goRef  q  qm x 
               g2 <- goProd qm q' r
               return $ fmap (\a k -> k a) g1 <*> g2) qs 

    goRef :: forall s a. Q -> Q -> Ref s (RHS s inc a) -> FuseM s inc outc (OpenGrammar s outc a)
    goRef q q' x = do
      tbRef <- ask
      tb    <- lift $ readRef tbRef
      case M2.lookup (RefTuple x (q,q')) tb of
        Just v  -> return v
        Nothing -> do
          rhs <- lift $ readRef x
          rec res <- do
                lift $ writeRef tbRef (M2.insert (RefTuple x (q,q')) res tb)
                g <- goRHS q q' rhs 
                r <- newRef $ LazyRHS $ runOpenG g
                return $ OpenG $ return $ RSingle (PSymb (NT r))
          return res 


type GGM s c = ReaderT (Ref s (Map2 (RefK s (RHS s c)) (RefK s (RHS s c)))) (RefM s)

optSpaces :: Grammar ExChar a -> Grammar ExChar a
optSpaces g = fuseWithTransducer (preprocess g) tr
  where
    tr = Transducer 0 [0,1,2] [0,1,2] (Trans trC trF)
    trC 0 Space  = ([], 1)
    trC 0 Spaces = ([], 2)
    trC 0 (NormalChar c) = ([NormalChar c], 0)

    trC 1 Space  = ([Space], 1)
    trC 1 Spaces = ([Space], 2)
    trC 1 (NormalChar c) = ([Space, NormalChar c], 0)

    trC 2 Space  = ([Space],  2)
    trC 2 Spaces = ([],       2)
    trC 2 (NormalChar c) = ([Spaces, NormalChar c], 0)

    trC _ _ = error "Cannot happen"

    trF 0 = Just []
    trF 1 = Just [Space]
    trF 2 = Just [Spaces]
    trF _ = error "Cannot happen" 


    preprocess :: Grammar ExChar a -> Grammar ExChar a
    preprocess (Grammar m) = Grammar $ do 
      ref <- m
      tbRef <- newRef $ M2.empty
      NT ref' <- runReaderT (goSymb (NT ref)) tbRef
      return ref' 
        where
          goRHS :: RHS s ExChar a -> GGM s ExChar (RHS s ExChar a)
          goRHS (RHS rs b) = do
            rs' <- mapM goProd (norm rs b)
            return $ RHS rs' b

          goProd :: Prod s ExChar a -> GGM s ExChar (Prod s ExChar a)
          goProd (PNil f) = return $ PNil f
          goProd (PCons s r) = do
            s' <- goSymb s
            r' <- goProd r
            return $ PCons s' r'

          goSymb :: Symb RHS s ExChar a -> GGM s ExChar (Symb RHS s ExChar a)
          goSymb (Term c) = return (Term c)
          goSymb (NT x)   = do
            tbRef <- ask
            tb <- lift $ readRef tbRef
            case M2.lookup (coerce x) tb of
              Just y -> return $ NT (coerce y)
              Nothing -> do
                rhs <- readRef x 
                rec y <- do
                      writeRef tbRef (M2.insert (coerce x) (coerce y) tb)
                      rhs' <- goRHS rhs 
                      newRef rhs'
                return $ NT y 
                      
            
            

          norm :: [Prod s ExChar a] -> Maybe (a :~: ()) -> [Prod s ExChar a]
          norm ss Nothing     = ss
          norm ss (Just Refl) = norm' False $ sortBy cmp ss
            where
              cmp :: Prod s ExChar a -> Prod s ExChar b -> Ordering
              cmp (PNil _) (PCons _ _)    = LT
              cmp (PNil _) (PNil _)       = EQ 
              cmp (PCons _ _) (PNil _)    = GT
              cmp (PCons _ a) (PCons _ b) = cmp a b 

          norm' :: Bool -> [Prod s ExChar ()] -> [Prod s ExChar  ()]
          norm' _ (PNil _:ss) = norm' True ss
          norm' True (PCons (Term Space) (PCons (Term Spaces) (PNil _)):ss) = PCons (Term Space) (PNil $ const ()):norm' True ss
          norm' b (s:ss) = s:norm' b ss
          norm' b [] = if b then [PNil ()] else [] 

            
      
      

_example1 :: Grammar ExChar ()
_example1 = finalize $ do
  rec p <- share $
           text "(" *> p <* text ")" <* p
           <|> pure ()
  return p 


_example2 :: Grammar ExChar [ExChar]
_example2 = finalize $ do
  rec alpha     <- share $ foldr1 (<|>) $ map char ['a'..'z']
      alphas    <- share $ (:) <$> alpha <*> alphaStar
      alphaStar <- share $ pure [] <|> alphas
  return alphas 

_example3 :: Grammar ExChar [ExChar]
_example3 = finalize $ do
  rec alphas    <- do
        alpha     <- share $ foldr1 (<|>) $ map char ['a'..'z']
        alphaStar <- share $ pure [] <|> alphas
        share $ (:) <$> alpha <*> alphaStar
  return alphas



_example4 :: Grammar ExChar ()
_example4 = finalize $ do
  rec alphas <- do 
        alpha     <- share $ foldr1 (<|>) $ map char ['a'..'z']
        alphaStar <- share $ pure [] <|> alphas
        share $ (:) <$> alpha <*> alphaStar
  rec tree    <- share $ pure () <* alphas <* spaces <* text "[" <* spaces <* forest <* spaces <* text "]"
      forest  <- share $ pure () <|> forest1 
      forest1 <- share $
                 tree
                 <|> tree *> spaces <* text "," <* spaces <* forest1
  return tree 
  
                  
