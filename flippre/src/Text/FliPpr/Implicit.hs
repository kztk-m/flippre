{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Text.FliPpr.Implicit (
  define,
  Materializable (..),
  materializeWithProxy,
  unMaterializeWithProxy,
) where

import Data.Bits (Bits (shiftR, xor, (.&.)))
import qualified Data.Fin as F
import Data.Int (Int8)
import Data.Kind (Type)
import qualified Data.Type.Nat as F
import Data.Word (Word8)
import qualified Defs
import Text.FliPpr.Internal.Core

materializeWithProxy :: (Materializable a) => proxy a -> a -> Store a
materializeWithProxy _ = materialize

unMaterializeWithProxy :: (Materializable a) => proxy a -> Store a -> a
unMaterializeWithProxy _ = unMaterialize

-- | Inspired by https://hackage.haskell.org/package/memoize
class Materializable a where
  -- | *First-order* (non-function) datatype to store each computation result
  type Store a :: Type -- should not contain function types

  materialize :: a -> Store a
  unMaterialize :: Store a -> a

-- | 'define' marks a definition of FliPpr function. This function is merely
-- defined as:
--
-- > define f = unMaterialize (materialize f)
--
-- This definition relies on how GHC evaluates expressions. For example, for @h
-- :: (bool -> Exp Implicit v D) -> bool -> Exp Implicit v D@,
--
-- > f = define $ h f
--
-- is equivalent to
--
-- > f b = if b then s1 else s2
-- >   where (s1 , s2) = (h f true, h f false)
--
-- in GHC.
define :: (Materializable a) => a -> a
define f = unMaterialize s
  where
    s = materialize f
{-# INLINEABLE define #-}

instance (Materializable a, Materializable b) => Materializable (a, b) where
  type Store (a, b) = (Store a, Store b)
  materialize (a, b) = (materialize a, materialize b)
  {-# INLINEABLE materialize #-}
  unMaterialize (s1, s2) = (unMaterialize s1, unMaterialize s2)

instance (s ~ Implicit) => Materializable (Exp s v a) where
  type Store (Exp s v a) = Exp s v a
  materialize = id
  {-# INLINE materialize #-}
  unMaterialize = id
  {-# INLINE unMaterialize #-}
instance (Repr Implicit v r) => Materializable (In v a -> r) where
  type Store (In v a -> r) = Exp Implicit v (a ~> ReprT r)

  materialize = fromFunction
  {-# INLINEABLE materialize #-}
  unMaterialize = toFunction

{-# ANN StoreLazy "HLINT: ignore Use newtype instead of data" #-}
data StoreLazy a = StoreLazy a

instance (Materializable r) => Materializable (() -> r) where
  type Store (() -> r) = StoreLazy (Store r)

  materialize f = StoreLazy (materialize $ f ())
  {-# INLINEABLE materialize #-}
  unMaterialize (StoreLazy s) = const $ unMaterialize s

instance (Materializable r) => Materializable (Bool -> r) where
  type Store (Bool -> r) = (Store r, Store r)
  materialize f = (materialize $ f True, materialize $ f False)
  {-# INLINEABLE materialize #-}
  unMaterialize (strue, sfalse) = \case
    True -> unMaterialize strue
    False -> unMaterialize sfalse

data BinSearchTree a = Leaf a | Bin (BinSearchTree a) (BinSearchTree a)
  deriving stock Functor
  deriving stock Show

makeTree :: Int -> Int -> BinSearchTree Int
makeTree lower upper
  | lower == upper = Leaf lower
  | otherwise =
      let mid = midpoint lower upper
      in  Bin (makeTree lower mid) (makeTree (mid + 1) upper)

-- Compute the middle point of two integers without overflow.
--
-- See:
-- https://lemire.me/blog/2022/12/06/fast-midpoint-between-two-integers-without-overflow/
-- https://stackoverflow.com/questions/74254168/how-to-get-the-mid-of-2-int32-number-elegantly-without-overflow
midpoint :: Int -> Int -> Int
midpoint x y = (x .&. y) + (xor x y `shiftR` 1)

lookupTree ::
  Int
  -- ^ lower bound (inclusive)
  -> Int
  -- ^ upper bound (inclusive)
  -> Int
  -- ^ index (invariant: lower <= index <= upper)
  -> BinSearchTree a
  -> a
lookupTree lower upper !idx b
  | lower == upper = case b of
      Leaf a -> a
      Bin _ _ -> error "IMPOSSIBLE"
  | otherwise = case b of
      Bin left right ->
        let mid = midpoint lower upper
        in  if idx <= mid
              then lookupTree lower mid idx left
              else lookupTree (mid + 1) upper idx right
      Leaf _ -> error "IMPOSSIBLE"

instance (Materializable r, Enum a, Bounded a) => Materializable (Defs.FromBounded a -> r) where
  type Store (Defs.FromBounded a -> r) = BinSearchTree (Store r)

  materialize = \f ->
    materialize . f . Defs.FromBounded . toEnum <$> makeTree lower upper
    where
      lower = fromEnum (minBound :: a)
      upper = fromEnum (maxBound :: a)
  {-# INLINEABLE materialize #-}

  unMaterialize t =
    \idx -> unMaterialize $ lookupTree lower upper (fromEnum idx) t
    where
      lower = fromEnum (minBound :: a)
      upper = fromEnum (maxBound :: a)

deriving via (Defs.FromBounded Int -> r) instance (Materializable r) => Materializable (Int -> r)
deriving via (Defs.FromBounded Word -> r) instance (Materializable r) => Materializable (Word -> r)
deriving via (Defs.FromBounded Word8 -> r) instance (Materializable r) => Materializable (Word8 -> r)
deriving via (Defs.FromBounded Int8 -> r) instance (Materializable r) => Materializable (Int8 -> r)

deriving via
  (Defs.FromBounded (F.Fin n) -> r)
  instance
    (Materializable r, F.SNatI m, F.S m ~ n) => Materializable (F.Fin n -> r)

instance
  (Materializable (a -> r), Materializable (b -> r)) =>
  Materializable (Either a b -> r)
  where
  type Store (Either a b -> r) = (Store (a -> r), Store (b -> r))

  materialize f = (materialize (f . Left), materialize (f . Right))
  {-# INLINEABLE materialize #-}

  unMaterialize (sl, sr) = \case
    Left a -> unMaterialize sl a
    Right b -> unMaterialize sr b

instance
  (Materializable (a -> b -> r)) =>
  Materializable ((a, b) -> r)
  where
  type Store ((a, b) -> r) = Store (a -> b -> r)

  materialize f = materialize (curry f)
  {-# INLINEABLE materialize #-}
  unMaterialize s = uncurry (unMaterialize s)