{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}

module Text.FliPpr.Internal.CPS where

newtype CPS e a = CPS { runCPS :: forall r. (a -> e r) -> e r }
  -- ^ r is universally quantified and may have a kind other than "*". 


instance Functor (CPS e) where
  fmap f (CPS m) = CPS $ \k -> m (k . f)

instance Applicative (CPS e) where
  pure a = CPS $ \k -> k a
  CPS cf <*> CPS ca = CPS $ \k ->
    cf $ \f -> ca $ \a -> k (f a)

instance Monad (CPS e) where
  CPS cm >>= f = CPS $ \k -> cm $ \a -> runCPS (f a) k

unCPS :: CPS e (e r) -> e r
unCPS x = runCPS x id 

adjustCont2 :: (forall a. e a -> e' a) ->
            (forall a. e' a -> e a) ->
            CPS e a -> CPS e' a
adjustCont2 f fi (CPS m) = CPS $ \k -> f (m (fi . k))


cps :: (forall r. (a -> e r) -> e r) -> CPS e a 
cps = CPS 
