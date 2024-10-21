{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
-- | A minimal implementation of heterogeneous lists

module Text.FliPpr.Internal.HList
  (
    HList (..), Append, hAppend
  )
  where

import           Data.Kind (Type)

-- | @HList f '[a,b,c]@ denotes a heterogeneous list @f a, f b, f c@.
data HList (f :: k -> Type) :: [k] -> Type where
  HNil  :: HList f '[]
  HCons :: f a -> !(HList f as) -> HList f (a ': as)

instance (forall a. Show (f a)) => Show (HList f as) where
  showsPrec _ es = showString "[" . go es . showString "]"
    where
      go :: (forall a. Show (f a)) => HList f as' -> ShowS
      go HNil           = id
      go (HCons a HNil) = shows a
      go (HCons a as)   = shows a . showString "," . go as

type family Append (xs :: [k]) (ys :: [k]) :: [k] where
  Append '[]       ys = ys
  Append (x ': xs) ys = x ': Append xs ys

hAppend :: HList f as -> HList f bs -> HList f (Append as bs)
hAppend HNil ys         = ys
hAppend (HCons x xs) ys = HCons x (hAppend xs ys)

