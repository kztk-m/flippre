{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE RecursiveDo #-}
module Text.FliPpr.Internal.GrammarST where

import Control.Monad.ST
import Control.Monad.Reader
import Control.Monad.State
-- import Control.Monad.Fix

import Control.Applicative as A (Alternative(..), Const(..)) 

import Data.STRef
import Data.Function (on)

import Data.Typeable ((:~:)(..))
import Unsafe.Coerce 

import Data.Coerce 

import Text.FliPpr.Doc as D hiding (text)
import qualified Text.FliPpr.Doc as D 

import Data.Map2 (Ord2(..), Ordering2(..), Map2) 
import qualified Data.Map2 as M2 

import Data.List (sortBy)

import Data.Maybe (fromMaybe)
import qualified Data.IntMap as IM 
-- import qualified Data.IntSet as IS 

data Ref s a  = Ref !Int !(STRef s a)
type RefM s = ReaderT (STRef s Int) (ST s) 

class Monad m => MonadRef s m | m -> s where
  newRef   :: a -> m (Ref s a)
  readRef  :: Ref s a -> m a
  writeRef :: Ref s a -> a -> m () 


instance MonadRef s (RefM s) where 
  newRef a = do
    r <- ask
    i <- lift $ readSTRef r
    lift $ (writeSTRef r $! i+1)
    ref <- lift $ newSTRef a
    return (Ref i ref)

  readRef (Ref _ ref) = lift $ readSTRef ref

  writeRef (Ref _ ref) v = lift $ writeSTRef ref v

instance MonadRef s (ReaderT r (RefM s)) where
  newRef a = lift $ newRef a
  readRef ref = lift $ readRef ref
  writeRef ref a = lift $ writeRef ref a 


refID :: Ref s a -> Int
refID (Ref i _) = i

instance Eq (Ref s a) where
  (==) = (==) `on` refID

instance Ord (Ref s a) where
  compare = compare `on` refID 

eqRef :: Ref s a -> Ref s b -> Maybe (a :~: b)
eqRef (Ref i _) (Ref j _)
  | i == j    = Just (unsafeCoerce Refl)
  | otherwise = Nothing 

newtype Grammar c a = Grammar (forall s. RefM s (Ref s (RHS s c a)))
data RHS s c a = RHS [Prod s c a] (Maybe (a :~: ()))

data Prod s c a =
  forall r. PCons (Symb RHS s c r) (Prod s c (r -> a))
  | PNil a

data Symb rhs s c a where
  NT   :: Ref s (rhs s c a) -> Symb rhs s c a 
  Term :: c -> Symb rhs s c c 

type PprM s = StateT (IM.IntMap Doc) (ST s) 

instance Show c => Pretty (Grammar c a) where
  ppr (Grammar m) = runST $ do
    cref <- newSTRef 0 
    nt <- runReaderT m cref 
    tb <- execStateT (pprRefM nt) IM.empty
    return $ D.text "main: " <> pprNT nt </> 
      vcat (map pprEntry $ IM.toList tb)
      where
        pprEntry (k, d) = pprID k <+> D.text "=" <+> align d 
        pprID n = D.text ("P" ++ show n)
        pprNT n = pprID (refID n) 

        checkVisited :: Int -> PprM s Bool 
        checkVisited i = do
          tb <- get
          return $ IM.member i tb 

        updateTable :: Int -> Doc -> PprM s () 
        updateTable i v = do
          tb <- get
          put $! IM.insert i v tb 

        pprRefM :: forall s c a. Show c => Ref s (RHS s c a) -> PprM s Doc 
        pprRefM (Ref i ref) = do
          b <- checkVisited i 
          when (not b) $ do            
            rhs <- lift $ readSTRef ref
            updateTable i D.empty 
            d <- pprRHS rhs
            updateTable i d
          return $ pprID i 

        pprRHS :: forall s c a. Show c => RHS s c a -> PprM s Doc 
        pprRHS (RHS rs b) =
          case b of
            Nothing ->  pprRHS' rs 
            Just _  ->  braces <$> pprRHS' rs  
          where
            pprRHS' [] = return $ D.text "<empty>"
            pprRHS' rs = arrange <$> mapM (fmap align . pprProd) rs
            
            arrange :: [Doc] -> Doc
            arrange [d1,d2]    = group (go [d1,d2])
            arrange [d1,d2,d3] = group (go [d1,d2,d3])
            arrange (d1:d2:d3:d4:ds) =
              group (go [d1,d2,d3,d4]) </> D.text "|" <+> arrange ds
            arrange ds = group (go ds) 
            
            go []     = D.empty 
            go [d]    = d
            go (d:ds) = d </> D.text "|" <+> go ds 

        pprProd :: forall s c a. Show c => Prod s c a -> PprM s Doc 
        pprProd (PNil _)  = return $ D.text (show "")
        pprProd p         = go [] p
          where
            go :: forall s c a. Show c => [c] -> Prod s c a -> PprM s Doc
            go s (PNil _) = return $ D.text (show (reverse s))
            go s (PCons (Term c) (PNil _)) = return $ D.text (show $ reverse $ c:s)
            go s (PCons (Term c) r) = go (c:s) r
            go s (PCons (NT n) (PNil _)) = do 
              dn <- pprRefM n
              return $ pprS (reverse s) dn
            go s (PCons (NT n) r) = do
              dn <- pprRefM n
              dr <- go [] r
              return $ pprS (reverse s) (dn <+> dr) 

            pprS [] d = d
            pprS s  d = D.text (show s) <+> d 

instance Show c => Show (Grammar c a) where
  show = show . ppr 
            

newtype OpenGrammar s c a = OpenG { runOpenG :: RefM s (OpenRHS s c a) } 
data OpenRHS s c a where
  RUnion  :: OpenRHS s c a -> OpenRHS s c a -> OpenRHS s c a
  REmpty  :: OpenRHS s c a
  RUnInit :: OpenRHS s c a
  RSingle :: OpenProd s c a -> OpenRHS s c a 
  RVoid   :: OpenRHS s c () -> OpenRHS s c () 

runion :: OpenRHS s c a -> OpenRHS s c a -> OpenRHS s c a
runion REmpty r = r
runion r REmpty = r
runion (RVoid r1) r2 = rvoid (runion r1 r2)
runion r1 (RVoid r2) = rvoid (runion r1 r2)
runion r1 r2         = RUnion r1 r2

rvoid :: OpenRHS s c () -> OpenRHS s c ()
rvoid (RVoid r) = RVoid r
rvoid REmpty    = REmpty
rvoid RUnInit   = RUnInit
rvoid r         = RVoid r 

newtype LazyRHS s c a = LazyRHS (RefM s (OpenRHS s c a))

data OpenProd s c a where 
  PSymb :: Symb LazyRHS s c a -> OpenProd s c a 
  PMult :: OpenProd s c (a -> b) -> OpenProd s c a -> OpenProd s c b
  PPure :: a -> OpenProd s c a 

instance Functor (OpenGrammar s c) where
  fmap f (OpenG m) = OpenG $ fmap (fmap f) m

instance Functor (OpenProd s c) where
  fmap f x = pure f <*> x

instance Applicative (OpenProd s c) where
  pure  = PPure
  (<*>) = PMult
  
instance Functor (OpenRHS s c) where
  fmap f (RUnion r1 r2) = RUnion (fmap f r1) (fmap f r2)
  fmap f (RSingle r)    = RSingle (fmap f r)
  fmap f (RVoid r)      = fmap (f . const ()) r
  fmap _ REmpty         = REmpty
  fmap _ RUnInit        = RUnInit 

instance Applicative (OpenRHS s c) where
  pure = RSingle . PPure
  REmpty <*> _ = REmpty
  RUnion r1 r2 <*> r = runion (r1 <*> r) (r2 <*> r)
  RSingle _ <*> REmpty = REmpty
  RSingle p <*> (RUnion r1 r2) = runion (RSingle p <*> r1) (RSingle p <*> r2)
  RSingle p <*> RSingle q = RSingle (p <*> q)
  RSingle p <*> RVoid r   = RSingle p <*> r 
  _ <*> _ = error "Cannot happen."

instance Alternative (OpenRHS s c) where
  empty = REmpty
  (<|>) = runion 


atmostSingle :: OpenRHS s c a -> Bool
atmostSingle = (>0) . go 2
  where
    go :: Int -> OpenRHS s c a -> Int
    go lim _ | lim <= 0 = lim
    go lim (RSingle _)    = lim - 1
    go lim (RUnion r1 r2) = go (go lim r1) r2
    go lim (RVoid r)      = go lim r
    go lim _              = lim 

instance Applicative (OpenGrammar s c) where
  pure a = OpenG $ return $ pure a  

  OpenG m1 <*> OpenG m2 = OpenG $ do
    r1 <- m1 >>= tryShareRHS 
    r2 <- m2 >>= tryShareRHS 
    return $ r1 <*> r2
      where 
        tryShareRHS :: OpenRHS s c a -> RefM s (OpenRHS s c a)
        tryShareRHS rhs =
          if atmostSingle rhs then
            return rhs
          else do 
            r <- newRef (LazyRHS $ return rhs)
            return $ RSingle (PSymb (NT r))

instance Alternative (OpenGrammar s c) where
  empty = OpenG $ return A.empty
  OpenG m1 <|> OpenG m2 = OpenG $ liftM2 (<|>) m1 m2 
  
    

share :: OpenGrammar s c a -> RefM s (OpenGrammar s c a)
share (OpenG m) = do
  ref <- newRef $ LazyRHS $ m
  return $ OpenG (return (RSingle (PSymb (NT ref))))
  -- r <- mfix $ \_ -> do
  --   rhs <- m
  --   newRef rhs
  -- return $ OpenG $ return $ RSingle (PSymb (NT r))

instance M2.Eq2 (Ref s) 
instance Ord2 (Ref s) where
  compare2 r1 r2
    | refID r1 < refID r2 = LT2
    | refID r1 > refID r2 = GT2
    | otherwise           =
        case eqRef r1 r2 of
          Just Refl -> EQ2
          Nothing   -> error "Cannot happen" 
      
        
-- newtype RefMap s k1 k2 = RefMap { runRefMap :: forall a. Ref s (k1 a) -> Maybe (Ref s (k2 a)) }

-- lookupRefMap :: Ref s (k1 a) -> RefMap s k1 k2 -> Maybe (Ref s (k2 a))
-- lookupRefMap s (RefMap k) = k s

-- insertRefMap :: Ref s (k1 a) -> Ref s (k2 a) -> RefMap s k1 k2 -> RefMap s k1 k2
-- insertRefMap x v (RefMap f) = RefMap $ \x' ->
--   case eqRef x' x of
--     Just Refl -> return v
--     Nothing   -> f x'

newtype RefK s k a = RefK { unRefK :: Ref s (k a) } 

instance M2.Eq2 (RefK s k) 
instance Ord2 (RefK s k) where
  compare2 (RefK x) (RefK y) =
    case compare2 x y of
      LT2 -> LT2
      GT2 -> GT2
      EQ2 -> EQ2 

type RefRefMap s k1 k2 = Map2 (RefK s k1) (RefK s k2)

lookupRefRefMap :: Ref s (k1 a) -> RefRefMap s k1 k2 -> Maybe (Ref s (k2 a))
lookupRefRefMap x m = unRefK <$> M2.lookup (RefK x) m

insertRefRefMap :: Ref s (k1 a) -> Ref s (k2 a) -> RefRefMap s k1 k2 -> RefRefMap s k1 k2
insertRefRefMap x y = M2.insert (RefK x) (RefK y) 


type FinalizeM s c = ReaderT (Ref s (RefRefMap s (LazyRHS s c) (RHS s c))) (RefM s) 

finalize :: (forall s. RefM s (OpenGrammar s c a)) -> Grammar c a
finalize m = Grammar $ do
  rhs <- join (fmap runOpenG m) 
  refMap <- newRef $ M2.empty
  case rhs of
    RSingle (PSymb (NT x)) -> do 
      NT x' <- runReaderT (finalizeSymb (NT x)) refMap
      return x' 
    _ -> do 
      rhs' <- runReaderT (finalizeRHS rhs) refMap 
      ref <- newRef rhs'
      return $ ref 

finalizeRHS :: OpenRHS s c a -> FinalizeM s c (RHS s c a)
finalizeRHS = \r -> go r (RHS [] Nothing) 
  where
    go :: OpenRHS s c a -> RHS s c a -> FinalizeM s c (RHS s c a)
    go REmpty         r = return r
    go RUnInit        r = return r
    go (RUnion r1 r2) r = go r2 r >>= go r1 
    go (RSingle p)    r = do
      let RHS ps w = r
      p' <- case w of
              Just Refl -> finalizeProdV p
              Nothing   -> finalizeProd  p 
      return $ RHS (p':ps) w 
    go (RVoid r) ~(RHS ps _) = go r (RHS ps (Just Refl)) 

finalizeProdV :: OpenProd s c () -> FinalizeM s c (Prod s c ())
finalizeProdV = fnaive ()
  where
    fnaive :: b -> OpenProd s c a -> FinalizeM s c (Prod s c b)
    fnaive f (PPure _)   = return $ PNil f
    fnaive f (PSymb s)   = do 
      s' <- finalizeSymb s
      return $ PCons s' (PNil (const f))
    fnaive f (PMult p q) = go f p (\g -> fnaive g q)

    go :: b -> OpenProd s c x -> (forall r. r -> FinalizeM s c (Prod s c r)) -> FinalizeM s c (Prod s c b) 
    go f (PPure _) r   = r f
    go f (PSymb s) r   = do
      s' <- finalizeSymb s
      PCons s' <$> r (const f)
    go f (PMult p q) r = go f p (\k -> go k q r)                            
       

finalizeProd :: OpenProd s c a -> FinalizeM s c (Prod s c a)
finalizeProd = fnaive id
  where
    fnaive :: (a -> b) -> OpenProd s c a -> FinalizeM s c (Prod s c b)
    fnaive f (PPure a)   = return $ PNil (f a)
    fnaive f (PSymb s)   = do
      s' <- finalizeSymb s
      return $ PCons s' (PNil f)
    fnaive f (PMult p q) = go (f.) p (\g -> fnaive g q)

    go :: (x -> (a -> b)) -> OpenProd s c x -> (forall r. (a -> r) -> FinalizeM s c (Prod s c r)) -> FinalizeM s c (Prod s c b)
    go f (PPure a) r = r (f a)
    go f (PSymb s) r = do
      s' <- finalizeSymb s
      PCons s' <$> r (flip f)
    go f (PMult p q) r =
      go (flip ($) . (f.)) p (\k -> go (\a b -> k (\f -> f a b)) q r)



finalizeSymb :: Symb LazyRHS s c a -> FinalizeM s c (Symb RHS s c a) 
finalizeSymb (Term c) = return (Term c)
finalizeSymb (NT ref)   = do
  rm <- ask 
  rMap <- lift $ readRef rm
  case lookupRefRefMap ref rMap of
    Just v  -> return $ NT v
    Nothing -> do 
      ref' <- lift $ newRef $ RHS [] Nothing 
      lift $ writeRef rm $! insertRefRefMap ref ref' rMap
      LazyRHS m <- lift $ readRef ref
      rhs' <- lift m >>= finalizeRHS 
      lift $ writeRef ref' rhs'
      return $ NT ref'


data ExChar = NormalChar Char | Space | Spaces 

instance Pretty ExChar where
  ppr (NormalChar c) = ppr c
  ppr Space          = D.text "_"
  ppr Spaces         = D.text "<spaces>"

  pprList = uncurry pprList' . chars []
    where
      chars s (NormalChar c:cs) = chars (c:s) cs
      chars s r                 = (reverse s, r)

      pprList' [] []     = D.text ""      
      pprList' [] (c:cs) = ppr c D.<+> pprList cs
      pprList' s  [] = D.ppr s
      pprList' s  r  = D.ppr s D.<+> pprList r 

instance Show ExChar where
  show       = show . ppr
  showList s = \r -> show (pprList s) ++ r 


class CharLike c where
  fromChar :: Char -> c 

instance CharLike ExChar where
  fromChar = NormalChar 

term :: c -> OpenGrammar s c c
term c = OpenG $ return $ RSingle (PSymb (Term c))

char :: CharLike c => Char -> OpenGrammar s c c
char c = term (fromChar c)

text :: CharLike c => String -> OpenGrammar s c [c]
text s = OpenG $ return $ RSingle $ fromText s
  where
    fromText :: CharLike c => String -> OpenProd s c [c]
    fromText []     = pure []
    fromText (c:cs) = (:) <$> PSymb (Term $ fromChar c) <*> fromText cs


discard :: OpenGrammar s c a -> OpenGrammar s c ()
discard (OpenG m) = OpenG $ fmap (rvoid . fmap (const ())) m
  
space :: OpenGrammar s ExChar ()
space = discard $ term Space 

spaces :: OpenGrammar s ExChar ()
spaces = discard $ term Spaces


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

newtype BoolR s c a = BoolR Bool

-- FIXME: Debug.
removeNonProductive :: Grammar c a -> Grammar c a
removeNonProductive (Grammar m) = finalize $ do
  ref <- m 
  pmRef <- newRef M2.empty
  pm <- check pmRef ref
  removeSymb pm (NT ref)
  where
    check pmRef ref = do
      pm <- readRef pmRef
      viRef <- newRef M2.empty
      _ <- checkSymb pmRef viRef (NT ref)
      pm' <- readRef pmRef
      if eqMap pm pm' then return pm else check pmRef ref
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

    checkRHS :: Ref s (Map2 (RefK s (RHS s c)) (Const Bool)) -> Ref s (Map2 (RefK s (RHS s c)) (Const ())) -> RHS s c a -> RefM s Bool 
    checkRHS pmRef viRef (RHS rs _) =
      or <$> mapM (checkProd pmRef viRef) rs

    checkProd :: Ref s (Map2 (RefK s (RHS s c)) (Const Bool)) -> Ref s (Map2 (RefK s (RHS s c)) (Const ())) -> Prod s c a -> RefM s Bool 
    checkProd _     _     (PNil _) = return True
    checkProd pmRef viRef (PCons s r) = do
      sb <- checkSymb pmRef viRef s
      rb <- checkProd pmRef viRef r
      return $ sb && rb      
    
    checkSymb _ _ (Term _) = return True 
    checkSymb pmRef viRef (NT ref) = do
      pm <- readRef pmRef
      vm <- readRef viRef
      case M2.lookup (coerce ref) vm of
        Just _ ->
          return $ fromMaybe False $ fmap getConst (M2.lookup (coerce ref) pm)
        Nothing -> do 
          writeRef viRef (M2.insert (coerce ref) (Const ()) vm)
          rhs <- readRef ref 
          b <- checkRHS pmRef viRef rhs
          writeRef pmRef (M2.insert (coerce ref) (Const b) pm)
          return b

    removeSymb :: Map2 (RefK s (RHS s c)) (Const Bool) -> Symb RHS s c a -> RefM s (OpenGrammar s c a)
    removeSymb pm =
      let TT _ _ f = foldGrammar
            (return A.empty)
            (\x y -> return $ x <|> y)
            (\_ -> return)
            (return . pure)
            (\x y -> return $ fmap (\a k -> k a) x <*> y)
            (return . term)
            (\x res -> case M2.lookup (RefK x) pm of
                Just (Const False) -> return A.empty
                _                  -> do
                  r <- newRef $ LazyRHS $ runOpenG res
                  return $ OpenG $ return $ RSingle $ PSymb $ NT r                      
                     )
      in f
    

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

    unions :: forall f a. Alternative f => [f a] -> f a 
    unions = foldr (<|>) A.empty 

    tryDiscard :: forall a s c. Maybe (a :~: ()) -> OpenGrammar s c a -> OpenGrammar s c a
    tryDiscard Nothing g     = g
    tryDiscard (Just Refl) g = discard g 

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

            
      
      

example1 :: Grammar ExChar ()
example1 = finalize $ do
  rec p <- share $
           text "(" *> p <* text ")" <* p
           <|> pure ()
  return p 


example2 :: Grammar ExChar [ExChar]
example2 = finalize $ do
  rec alpha     <- share $ foldr1 (<|>) $ map char ['a'..'z']
      alphas    <- share $ (:) <$> alpha <*> alphaStar
      alphaStar <- share $ pure [] <|> alphas
  return alphas 

example3 :: Grammar ExChar [ExChar]
example3 = finalize $ do
  rec alphas    <- do
        alpha     <- share $ foldr1 (<|>) $ map char ['a'..'z']
        alphaStar <- share $ pure [] <|> alphas
        share $ (:) <$> alpha <*> alphaStar
  return alphas



example4 :: Grammar ExChar ()
example4 = finalize $ do
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
  

-- -- data Cyclic s f a = forall b. CMult   (Cyclic s f (b -> a)) (Cyclic s f b) 
-- --                   | CPure   a
-- --                   | CRef    (Ref s (RefM s (Cyclic s f a)))

-- data CyclicA s f a = CPure a
--                    | forall b. CMult (CyclicA s f (b -> a)) (CArg s f b)

-- data CArg s f a = CNonRec (f a)
--                 | CRec    (Ref s (CyclicA s f a))
                   

-- resolveRef :: Ref s (RefM s (CyclicA s f a)) -> RefM s (CyclicA s f a)
-- resolveRef ref = do
--   tbRef <- newRef IS.empty
--   goRef tbRef ref
--   where
--     goRef :: Ref s IS.IntSet -> Ref s (RefM s (CyclicA s f a)) -> RefM s (CyclicA s f a)
--     goRef tbRef ref = do
--       tb <- readRef tbRef
--       case IS.member (refID ref) tb of
--         True  -> error "Loop"
--         False -> do 
--           m <- readRef ref
--           writeRef tbRef $! IS.insert (refID ref) tb
--           v <- m 
--           v' <- goV tbRef v
--           writeRef ref (return v')
--           return v' 
--     goV :: Ref s IS.IntSet -> CyclicA s f a -> RefM s (CyclicA s f a)
--     goV _     (CPure a)   = return (CPure a) 
--     goV _     (CMult f x) = return (CBranch m)
--     goV tbRef (CRef ref)  = goRef tbRef ref 

-- mapST :: Traversable f => (a -> RefM s b) -> Cyclic s f a -> RefM s (Cyclic s f b)
-- mapST f x = do
--   tbRef <- newRef IM.empty
--   go tbRef x
--   where
--     go tbRef (CBranch m) = CBranch <$> traverse (go tbRef) m
--     go tbRef (CRef r)    = do
--       tb <- readRef tbRef
--       case IM.lookup (refID r) tb of
--         Just v  -> return v
--         Nothing -> do
--           r' <- newRef (return undefined) 
--           writeRef tbRef $! IM.insert (refID r) (CRef r') tb
--           writeRef r' (resolveRef r >>= go tbRef)
--           return $ CRef r' 
      
      
                  
