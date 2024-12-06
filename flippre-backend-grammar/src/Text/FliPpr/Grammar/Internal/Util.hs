{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module Text.FliPpr.Grammar.Internal.Util where

import Control.Applicative (Const (..))
import Data.Maybe (fromJust)
import Data.Monoid (Endo (..))
import Data.Typeable ((:~:) (..))
import qualified Text.FliPpr.Grammar.Internal.Map2 as M2
import Text.FliPpr.Grammar.Types
import qualified Unsafe.Coerce

eqIx :: Ix env a -> Ix env b -> Maybe (a :~: b)
eqIx IxZ IxZ = Just Refl
eqIx (IxS x) (IxS y) = eqIx x y
eqIx _ _ = Nothing

envToMap :: Env f as -> M2.Map2 (IxN as) f
envToMap es =
  appEndo (getConst $ traverseEnvWithIxN (\ix e -> Const $ Endo (M2.insert ix e)) es) M2.empty

lookIxMap :: M2.Map2 (IxN env) f -> IxN env a -> f a
lookIxMap m x = fromJust $ M2.lookup x m

traverseEnvWithIxN :: forall m f g as. (Applicative m) => (forall a. IxN as a -> f a -> m (g a)) -> Env f as -> m (Env g as)
traverseEnvWithIxN f = go (IxN 0 IxZ)
  where
    -- unsafe implementation, as we are reluctant to pay computation cost just for type safety
    go :: forall bs b as1. IxN bs b -> Env f as1 -> m (Env g as1)
    go _ ENil = pure ENil
    go ix (ECons e es) = ECons <$> f (Unsafe.Coerce.unsafeCoerce ix) e <*> go (ixS ix) es

    ixS :: IxN bs b -> IxN (b : bs) b
    ixS (IxN w x) = IxN (w + 1) (IxS x)
    {-# INLINE ixS #-}

-- traverseEnvWithIxN _ ENil = pure ENil
-- traverseEnvWithIxN f (ECons e es) = ECons <$> f (IxN 0 IxZ) e <*> traverseEnvWithIxN (f . ixS) es
--   where
--     ixS :: IxN as a -> IxN (b : as) a
--     ixS (IxN w x) = IxN (w + 1) (IxS x)

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
