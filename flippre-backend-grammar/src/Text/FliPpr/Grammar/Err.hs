{-# LANGUAGE CPP #-}

-- | This module implements a monad `Err` which is isomorphic to @Either Doc@.
module Text.FliPpr.Grammar.Err (Err (..), err) where

#if !MIN_VERSION_base(4,11,0)
import qualified Control.Monad.Fail as Fail
#endif

import Data.String (IsString (..))
import qualified Prettyprinter as PP

-- | A datatype for handling errors, isomorphic to @Either (Doc ann)@.
data Err ann a
  = -- | successfull result
    Ok !a
  | -- | failed result with an error message.
    Fail !(PP.Doc ann)

instance Functor (Err ann) where
  fmap f (Ok a) = Ok (f a)
  fmap _ (Fail d) = Fail d
  {-# INLINE fmap #-}

instance Applicative (Err ann) where
  pure = Ok
  {-# INLINE pure #-}
  Fail d <*> Ok _ = Fail d
  Fail d <*> Fail d' = Fail (PP.vcat [d, d'])
  Ok _ <*> Fail d = Fail d
  Ok f <*> Ok a = Ok (f a)
  {-# INLINEABLE (<*>) #-}

instance Monad (Err ann) where
  return = pure
  {-# INLINE return #-}
  Fail d >>= _ = Fail d
  Ok a >>= f = f a
  {-# INLINE (>>=) #-}

#if !MIN_VERSION_base(4,11,0)
  fail = Fail.fail
#endif

instance MonadFail (Err ann) where
  fail = Fail . fromString

instance (Show a) => Show (Err ann a) where
  show (Ok a) = "Ok " ++ show a
  show (Fail s) = show (fromString "Error: " PP.<+> PP.align s)

-- | A synonym for 'Fail'.
err :: PP.Doc ann -> Err ann a
err = Fail
{-# INLINE err #-}
