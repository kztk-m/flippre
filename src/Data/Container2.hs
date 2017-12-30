{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}

module Data.Container2 where

import Data.Functor.Identity
import Control.Applicative (Const(..))
import Data.Monoid 

class Container2 t where
  traverse2 :: Applicative k => (forall a. f a -> k (g a)) -> t f -> k (t g)
  traverse2 f x = zipWithA2 (const f) x x 
  
  zipWithA2 :: Applicative k => (forall a. f a -> g a -> k (h a)) -> t f -> t g -> k (t h) 

fmap2 :: Container2 t => (forall a. f a -> g a) -> t f -> t g
fmap2 f = runIdentity . traverse2 (Identity . f)

length2 :: Container2 t => t f -> Int
length2 = foldr2 (const (+1)) 0 

foldr2 :: Container2 t => (forall a. f a -> r -> r) -> r -> t f -> r
foldr2 f b = flip appEndo b . getConst . traverse2 (Const . Endo . f) 

fold2 :: (Container2 t, Monoid m) => (forall a. f a -> m) -> t f -> m
fold2 f = getConst . traverse2 (Const . f)

zipWith2 :: Container2 t => (forall a. f a -> g a -> h a) ->
                            t f -> t g -> t h
zipWith2 f s t = runIdentity $ zipWithA2 (\x y -> Identity (f x y)) s t

data End f      = End 
data (a :< b) f = f a :< b f 

infixr 0 :< 

instance Container2 End where
  traverse2 _f End = pure End
  zipWithA2 _f End End = pure End 

instance Container2 r => Container2 (a :< r) where
  traverse2 f (a :< r) =
    (:<) <$> f a <*> traverse2 f r

  zipWithA2 f (a1 :< r1) (a2 :< r2) =
    (:<) <$> f a1 a2 <*> zipWithA2 f r1 r2 

newtype Single a f = Single (f a)
instance Container2 (Single a) where
  traverse2 f (Single x) = Single <$> f x 
  zipWithA2 f (Single x) (Single y) =
    Single <$> f x y 
