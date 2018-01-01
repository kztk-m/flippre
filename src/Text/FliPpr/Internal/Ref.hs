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


data Ref s a  = Ref !Int !(STRef s a)
type RefM s = ReaderT (STRef s Int) (ST s) 

runRefM :: (forall s. RefM s a) -> a
runRefM m = runST $ do
  iref <- newSTRef 0 
  runReaderT m iref
            

class Monad m => MonadRef s m | m -> s where
  newRef   :: a -> m (Ref s a)
  readRef  :: Ref s a -> m a
  writeRef :: Ref s a -> a -> m () 
  modifyRef :: Ref s a -> (a -> a) -> m ()
  modifyRef ref f = readRef ref >>= \a -> writeRef ref $! (f a)

instance MonadRef s (RefM s) where 
  newRef a = do
    r <- ask
    i <- lift $ readSTRef r
    lift $ (writeSTRef r $! i+1)
    ref <- lift $ newSTRef a
    return (Ref i ref)

  readRef (Ref _ ref) = lift $ readSTRef ref

  writeRef (Ref _ ref) v = lift $ writeSTRef ref $! v

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

instance Eq2 (Ref s) 
instance Ord2 (Ref s) where
  compare2 r1 r2
    | refID r1 < refID r2 = LT2
    | refID r1 > refID r2 = GT2
    | otherwise           =
        case eqRef r1 r2 of
          Just Refl -> EQ2
          Nothing   -> error "Cannot happen" 
      
        
