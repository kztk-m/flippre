{-# LANGUAGE CPP #-}

-- | This module implements a monad `Err` which is isomorphic to @Either Doc@.
module Text.FliPpr.Err (Err(..), err) where

#if !MIN_VERSION_base(4,11,0)
import qualified Control.Monad.Fail as Fail
#endif

import           Data.String        (IsString (..))
import qualified Prettyprinter      as PP

-- | A datatype to handling errors, isomorphic to @Either Doc@.
data Err a = Ok !a       -- ^ successfull result
           | Fail !(PP.Doc ()) -- ^ failed result with an error message.

instance Functor Err where
  fmap f (Ok a)   = Ok (f a)
  fmap _ (Fail d) = Fail d
  {-# INLINE fmap #-}

instance Applicative Err where
  pure = Ok
  {-# INLINE pure #-}
  Fail d <*> Ok _    = Fail d
  Fail d <*> Fail d' = Fail (PP.vcat[d, d'])
  Ok   _ <*> Fail d  = Fail d
  Ok   f <*> Ok a    = Ok (f a)
  {-# INLINABLE (<*>) #-}

instance Monad Err where
  return = pure
  {-# INLINE return #-}
  Fail d >>= _ = Fail d
  Ok a >>= f   = f a
  {-# INLINE (>>=) #-}

#if !MIN_VERSION_base(4,11,0)
  fail = Fail.fail
#endif

instance MonadFail Err where
  fail = Fail . fromString

instance Show a => Show (Err a) where
  show (Ok a)   = "Ok " ++ show a
  show (Fail s) = show (fromString "Error: " PP.<+> PP.align s)

-- | A synonym of 'Fail'.
err :: PP.Doc () -> Err a
err = Fail
{-# INLINE err #-}
