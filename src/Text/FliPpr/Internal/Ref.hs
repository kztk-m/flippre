{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}

module Text.FliPpr.Internal.Ref where

import Control.Monad.ST
import Control.Monad.Reader

import Data.STRef
import Data.Typeable ((:~:)(..))
import Unsafe.Coerce 

import Data.Function (on) 

import Data.Map2 (Ord2(..), Eq2(..), Ordering2(..)) 


data Ref s a  = Ref {-# UNPACK #-} !Int !(STRef s a)
type RefM s = ReaderT (STRef s Int) (ST s) 

runRefM :: (forall s. RefM s a) -> a
runRefM m = runST $ do
  iref <- newSTRef 0 
  runReaderT m iref
            

class Monad m => MonadRef s m | m -> s where
  newRef   :: a -> m (Ref s a)
  readRef  :: Ref s a -> m a
  writeRef :: Ref s a -> a -> m ()

  {-# INLINABLE modifyRef #-}
  modifyRef :: Ref s a -> (a -> a) -> m ()
  modifyRef ref f = readRef ref >>= \a -> writeRef ref $! (f a)

instance MonadRef s (RefM s) where 
  {-# INLINABLE newRef #-}
  newRef a = do
    r <- ask
    i <- lift $ readSTRef r
    lift $ (writeSTRef r $! i+1)
    ref <- lift $ newSTRef a
    return (Ref i ref)

  {-# INLINABLE readRef #-}
  readRef (Ref _ ref) = lift $ readSTRef ref

  {-# INLINABLE writeRef #-}
  writeRef (Ref _ ref) v = lift $ writeSTRef ref $! v

instance MonadRef s (ReaderT r (RefM s)) where
  {-# INLINABLE newRef #-}
  newRef a = lift $ newRef a
  {-# INLINABLE readRef #-}
  readRef ref = lift $ readRef ref
  {-# INLINABLE writeRef #-}
  writeRef ref a = lift $ writeRef ref a 


refID :: Ref s a -> Int
refID (Ref i _) = i

instance Eq (Ref s a) where
  {-# INLINABLE (==) #-}
  (==) = (==) `on` refID

instance Ord (Ref s a) where
  {-# INLINABLE compare #-}
  compare = compare `on` refID 

instance Eq2 (Ref s) where
  {-# INLINABLE eq2 #-}
  eq2 (Ref i _) (Ref j _)
    | i == j    = Just (unsafeCoerce Refl)
    | otherwise = Nothing 
  
instance Ord2 (Ref s) where
  {-# INLINABLE compare2 #-}
  compare2 r1 r2
    | refID r1 < refID r2 = LT2
    | refID r1 > refID r2 = GT2
    | otherwise           =
        case eq2 r1 r2 of
          Just Refl -> EQ2
          Nothing   -> error "Cannot happen" 
      
        