{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Text.FliPpr.Grammar.Internal.Util where

import Data.Typeable ((:~:) (..))
import Text.FliPpr.Grammar.Types

eqIx :: Ix env a -> Ix env b -> Maybe (a :~: b)
eqIx IxZ IxZ = Just Refl
eqIx (IxS x) (IxS y) = eqIx x y
eqIx _ _ = Nothing

zipWithEnvA :: (Applicative m) => (forall a. f a -> g a -> m (h a)) -> Env f as -> Env g as -> m (Env h as)
zipWithEnvA _ ENil ENil = pure ENil
zipWithEnvA f (ECons x xs) (ECons y ys) = ECons <$> f x y <*> zipWithEnvA f xs ys

traverseEnvWithIx :: (Applicative m) => (forall a. Ix as a -> f a -> m (g a)) -> Env f as -> m (Env g as)
traverseEnvWithIx = go id
  where
    go ::
      (Applicative m) =>
      (forall a. Ix as a -> Ix as0 a)
      -> (forall a. Ix as0 a -> f a -> m (g a))
      -> Env f as
      -> m (Env g as)
    go _ _ ENil = pure ENil
    go adj f (ECons e es) =
      let ix = adj IxZ
      in  ECons <$> f ix e <*> go (adj . IxS) f es
