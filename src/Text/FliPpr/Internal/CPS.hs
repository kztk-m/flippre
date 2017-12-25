{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}

module Text.FliPpr.Internal.CPS where


-- Notice that this monod is not the Codensity monad.
-- We do not expect e to be a monad, and we do restrict r to have
-- kind "*". 
newtype CPS e a = CPS { runCPS :: forall r. (a -> e r) -> e r }
  --

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
