{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}

{-# LANGUAGE RecursiveDo #-}

module Text.FliPpr.Internal.GrammarST.Core (

  -- ** Types
  -- *** Grammar for Manipulation
  Grammar(..), RHS(..), Prod(..), Symb(..),

  -- *** Grammar for Construction 
  OpenGrammar(..), OpenRHS(..), OpenProd(..), LazyRHS(..),

  -- *** Character type for manipulation
  ExChar(..), CharLike(..), 

  -- *** Parser I/F
  Driver(..), 

  -- ** Conversion
  finalize, open,

  -- ** Knot-Tying
  share,

  -- ** Primitives
  term, char, text, constantResult,
  space, spaces,

  -- ** Misc.
  atmostSingle, RefK(..)
  
  ) where

import Control.Monad.ST
import Control.Monad.Reader
import Control.Monad.State

import Control.Applicative as A (Alternative(..)) 

import Data.STRef
import qualified Data.IntMap as IM 

import Text.FliPpr.Doc as D hiding (text)
import qualified Text.FliPpr.Doc as D

import Data.Map2 (Ord2(..), Ordering2(..), Map2) 
import qualified Data.Map2 as M2 

import Text.FliPpr.Internal.Ref 
import Text.FliPpr.Err

newtype Grammar c a = Grammar (forall s. RefM s (Ref s (RHS s c a)))
newtype RHS s c a = RHS [Prod s c a] 

data Prod s c a =
  PNil a | forall r. PCons !(Symb RHS s c r) (Prod s c (r -> a))


data Symb rhs s c a where
  NT   :: !(Ref s (rhs s c a)) -> Symb rhs s c a 
  Term :: !c -> Symb rhs s c c 

type PprM s = StateT (IM.IntMap Doc) (ST s) 

instance Show c => Pretty (Grammar c a) where
  ppr (Grammar m) = runST $ do
    cref <- newSTRef 0 
    nt <- runReaderT m cref 
    tb <- execStateT (pprRefM nt) IM.empty
    return $ D.text "main: " <> pprNT nt </> 
      vcat (map pprEntry $ IM.toList tb)
      where
        pprEntry (k, d) = pprID k <+> align (D.text "=" <+> d)
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
        pprRHS (RHS rs) = pprRHS' rs 
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

instance Functor (Grammar c) where
  fmap f (Grammar m) = Grammar $ do
    r <- m
    ref <- newRef $ RHS [PCons (NT r) $ PNil f]
    return ref 

class Driver n where
  parse :: (Eq c, Pretty c) => n -> Grammar c (Err a) -> [c] -> Err [a]          

newtype OpenGrammar s c a = OpenG { runOpenG :: RefM s (OpenRHS s c a) } 
data OpenRHS s c a
  = RUnion (OpenRHS s c a) (OpenRHS s c a)
  | REmpty
  | RUnInit
  | RSingle (OpenProd s c a)
  | RConstant a (OpenRHS s c a) 

runion :: OpenRHS s c a -> OpenRHS s c a -> OpenRHS s c a
runion REmpty r = r
runion r REmpty = r
runion r1 r2               = RUnion r1 r2

rconstant :: t -> OpenRHS s c t -> OpenRHS s c t
rconstant _ (RConstant t r) = RConstant t r
rconstant _ REmpty    = REmpty
rconstant _ RUnInit   = RUnInit
rconstant t r         = RConstant t r 

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
  fmap f (RUnion r1 r2)  = RUnion (fmap f r1) (fmap f r2)
  fmap f (RSingle r)     = RSingle (fmap f r)
  fmap f (RConstant t r) = RConstant (f t) $ fmap (f . const t) r
  fmap _ REmpty          = REmpty
  fmap _ RUnInit         = RUnInit 

instance Applicative (OpenRHS s c) where
  pure a = RConstant a (RSingle (PPure a))

  REmpty <*> _ = REmpty
  RUnion r1 r2 <*> r = runion (r1 <*> r) (r2 <*> r)
  RSingle _ <*> REmpty = REmpty
  RSingle p <*> (RUnion r1 r2) = runion (RSingle p <*> r1) (RSingle p <*> r2)
  RSingle p <*> RSingle q = RSingle (p <*> q)
  RSingle p <*> RConstant _ r = RSingle p <*> r

  RConstant f r1 <*> RConstant a r2 = RConstant (f a) (r1 <*> r2)
  RConstant f r1 <*> (RUnion r2 r3) = runion (RConstant f r1 <*> r2) (RConstant f r1 <*> r3)
  RConstant _ r1 <*> r2       = r1 <*> r2 
  _ <*> _ = error "Cannot happen."

instance Alternative (OpenRHS s c) where
  empty = REmpty
  (<|>) = runion 


atmostSingle :: OpenRHS s c a -> Bool
atmostSingle = (>0) . go 2
  where
    go :: Int -> OpenRHS s c a -> Int
    go lim _ | lim <= 0    = lim
    go lim (RSingle _)     = lim - 1
    go lim (RUnion r1 r2)  = go (go lim r1) r2
    go lim (RConstant _ r) = go lim r 
    go lim _               = lim 

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
            case rhs of
              RConstant c _ ->
                return $ RConstant c $ RSingle $ PSymb $ NT r
              _ ->
                return $ RSingle $ PSymb $ NT r 

  g1 <* g2 = fmap (\a _ -> a) g1 <*> constantResult () g2
  g1 *> g2 = (constantResult (\a -> a) g1) <*> g2
  
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
  {-# INLINABLE compare2 #-}
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


type FinalizeM s c = ReaderT (RawRef s (RefRefMap s (LazyRHS s c) (RHS s c))) (RefM s) 

finalize :: (forall s. RefM s (OpenGrammar s c a)) -> Grammar c a
finalize m = Grammar $ do
  rhs <- join (fmap runOpenG m) 
  refMap <- newRawRef $ M2.empty
  case rhs of
    RSingle (PSymb (NT x)) -> do 
      NT x' <- runReaderT (finalizeSymb (NT x)) refMap
      return x' 
    _ -> do 
      rhs' <- runReaderT (finalizeRHS rhs) refMap 
      ref <- newRef rhs'
      return $ ref 

finalizeRHS :: OpenRHS s c a -> FinalizeM s c (RHS s c a)
finalizeRHS = \r -> RHS <$> (go Nothing r [])
  where
    go :: Maybe a -> OpenRHS s c a -> [Prod s c a] -> FinalizeM s c [Prod s c a]
    go _ REmpty         ps = return ps
    go _ RUnInit        ps = return ps
    go b (RUnion r1 r2) ps = go b r2 ps >>= go b r1 
    go b (RSingle p)    ps = do
      p' <- case b of
              Just t  -> finalizeProdV t p
              Nothing -> finalizeProd  p 
      return $ p':ps
    go _ (RConstant t r) ps = go (Just t) r ps 

finalizeProdV :: t -> OpenProd s c t -> FinalizeM s c (Prod s c t)
finalizeProdV t = fnaive t
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
  rMap <- lift $ readRawRef rm
  case lookupRefRefMap ref rMap of
    Just v  -> return $ NT v
    Nothing -> do 
      ref' <- lift $ newRef $ RHS []
      lift $ writeRawRef rm $! insertRefRefMap ref ref' rMap
      LazyRHS m <- lift $ readRef ref
      rhs' <- lift m >>= finalizeRHS 
      lift $ writeRef ref' rhs'
      return $ NT ref'

type OpenM s c = ReaderT (RawRef s (Map2 (RefK s (RHS s c)) (OpenGrammar s c))) (RefM s)

open :: Grammar c a -> OpenGrammar s c a
open (Grammar m) = OpenG $ do
  ref <- m 
  tbRef <- newRawRef M2.empty
  g <- runReaderT (goSymb (NT ref)) tbRef
  runOpenG g 
    where
      goSymb :: Symb RHS s c a -> OpenM s c (OpenGrammar s c a)
      goSymb (Term c) = return (term c)
      goSymb (NT ref) = do 
        tbRef <- ask
        tb <- readRawRef tbRef 
        case M2.lookup (RefK ref) tb of
          Just res -> return res
          Nothing  -> do
            rec res <- do
                  modifyRawRef tbRef (M2.insert (RefK ref) res)
                  rhs  <- readRef ref
                  g    <- goRHS rhs
                  ref' <- newRef $ LazyRHS (runOpenG g)
                  return $ OpenG $ return $ RSingle (PSymb (NT ref'))
            return res

      goRHS :: RHS s c a -> OpenM s c (OpenGrammar s c a)
      goRHS (RHS rs) = foldr (<|>) A.empty <$> mapM goProd rs

      goProd :: Prod s c a -> OpenM s c (OpenGrammar s c a)
      goProd (PNil a)    = return $ pure a
      goProd (PCons c r) =
        liftM2 (<*>) (fmap (\a k -> k a) <$> goSymb c) (goProd r)


            


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
      pprList' [] (c:cs) = case cs of { [] -> ppr c; _ -> ppr c D.<+> pprList cs }
      pprList' s  [] = D.ppr s
      pprList' s  r  = D.ppr s D.<+> pprList r 

instance Show ExChar where
  show       = show . ppr
  showList s = \r -> show (pprList s) ++ r 


class CharLike c where
  fromChar :: Char -> c 

instance CharLike Char where
  fromChar = id 

instance CharLike ExChar where
  fromChar = NormalChar 

term :: c -> OpenGrammar s c c
term c = OpenG $ return $ RConstant c $ RSingle (PSymb (Term c))

char :: CharLike c => Char -> OpenGrammar s c c
char c = term (fromChar c)

text :: CharLike c => String -> OpenGrammar s c [c]
text s = let ts = map fromChar s
         in OpenG $ return $ RConstant ts $ RSingle $ fromText ts
  where
    fromText :: [c] -> OpenProd s c [c]
    fromText []     = pure []
    fromText (c:cs) = (:) <$> PSymb (Term $ c) <*> fromText cs

-- | Same as @fmap . const@ but this would be useful for further optimization. 
constantResult :: t -> OpenGrammar s c a -> OpenGrammar s c t 
constantResult t (OpenG m) = OpenG $ fmap (rconstant t . fmap (const t)) m
  
space :: OpenGrammar s ExChar ()
space = constantResult () $ term Space 

spaces :: OpenGrammar s ExChar ()
spaces = constantResult () $ term Spaces
