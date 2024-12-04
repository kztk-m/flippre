{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Text.FliPpr.Grammar.Internal.Map2 (
  Ord2 (..),
  Eq2 (..),
  Ordering2 (..),
  Entry (..),
  Map2,
  lookup,
  insert,
  empty,
  adjust,
  toList,
  fromAscList,
) where

import Prelude hiding (lookup)

-- import Data.Container2
import Data.Typeable ((:~:) (..))
import Text.FliPpr.Grammar.Types (Ix (..))

data Ordering2 a b where
  LT2 :: Ordering2 a b
  GT2 :: Ordering2 a b
  EQ2 :: Ordering2 a a

class (Eq2 k) => Ord2 k where
  compare2 :: k a -> k b -> Ordering2 a b

class Eq2 k where
  eq2 :: k a -> k b -> Maybe (a :~: b)

instance Eq2 (Ix env) where
  eq2 IxZ IxZ = Just Refl
  eq2 (IxS x) (IxS y) = eq2 x y
  eq2 _ _ = Nothing

instance Ord2 (Ix env) where
  compare2 IxZ IxZ = EQ2
  compare2 IxZ (IxS _) = LT2
  compare2 (IxS _) IxZ = GT2
  compare2 (IxS x) (IxS y) = compare2 x y

-- default eq2 :: (Ord2 k) => k a -> k b -> Maybe (a :~: b)
-- eq2 x y = case compare2 x y of
--   EQ2 -> Just Refl
--   _ -> Nothing

data Entry k1 k2 = forall a. Entry (k1 a) (k2 a)

-- data Color = Red | Black
type Color = Int

pattern Red :: Color
pattern Red = 0

pattern Black :: Color
pattern Black = 1

data Map2 k1 k2
  = Leaf
  | Node {-# UNPACK #-} !Color !(Entry k1 k2) (Map2 k1 k2) (Map2 k1 k2)

lookup :: (Ord2 k1) => k1 a -> Map2 k1 k2 -> Maybe (k2 a)
lookup _ Leaf = Nothing
lookup x (Node _ (Entry y v) l1 l2) =
  case compare2 x y of
    LT2 -> lookup x l1
    GT2 -> lookup x l2
    EQ2 -> Just v

adjust :: (Ord2 k1) => (k2 a -> k2 a) -> k1 a -> Map2 k1 k2 -> Map2 k1 k2
adjust _ _ Leaf = Leaf
adjust f x (Node c e@(Entry y v) l1 l2) =
  case compare2 x y of
    LT2 -> Node c e (adjust f x l1) l2
    GT2 -> Node c e l1 (adjust f x l2)
    EQ2 -> Node c (Entry y (f v)) l1 l2

insert :: (Ord2 k1) => k1 a -> k2 a -> Map2 k1 k2 -> Map2 k1 k2
insert x0 v0 = makeBlack . go x0 v0
  where
    {-# INLINE makeBlack #-}
    makeBlack (Node _ e l1 l2) = Node Black e l1 l2
    makeBlack t = t

    go :: (Ord2 k1) => k1 a -> k2 a -> Map2 k1 k2 -> Map2 k1 k2
    go x v Leaf = Node Red (Entry x v) Leaf Leaf
    go x v (Node o e@(Entry y _) l1 l2) =
      case compare2 x y of
        LT2 -> node o e (insert x v l1) l2
        GT2 -> node o e l1 (insert x v l2)
        EQ2 -> Node o (Entry y v) l1 l2

    {-# INLINEABLE node #-}
    node :: Color -> Entry k1 k2 -> Map2 k1 k2 -> Map2 k1 k2 -> Map2 k1 k2
    node Black e3 (Node Red e2 (Node Red e1 x y) z) w = Node Red e2 (Node Black e1 x y) (Node Black e3 z w)
    node Black e3 (Node Red e1 x (Node Red e2 y z)) w = Node Red e2 (Node Black e1 x y) (Node Black e3 z w)
    node Black e1 x (Node Red e3 (Node Red e2 y z) w) = Node Red e2 (Node Black e1 x y) (Node Black e3 z w)
    node Black e1 x (Node Red e2 y (Node Red e3 z w)) = Node Red e2 (Node Black e1 x y) (Node Black e3 z w)
    node color e1 x y = Node color e1 x y

{-# INLINEABLE empty #-}
empty :: Map2 k1 k2
empty = Leaf

fromAscList :: (Ord2 k1) => [Entry k1 k2] -> Map2 k1 k2
fromAscList = \xs -> fst $ go False (length xs) xs
  where
    -- go b n es takes the first (if b then n else n-1) element from the list to
    -- return a tree together with the rest elements.
    go :: (Ord2 k1) => Bool -> Int -> [Entry k1 k2] -> (Map2 k1 k2, [Entry k1 k2])
    go False 1 (e : es) = (Node Red e Leaf Leaf, es)
    go True 1 es = (Leaf, es)
    go b n es
      | r' == 0 =
          case go b n' es of
            (l1, e : es1) ->
              let (l2, es2) = go True n' es1
              in  (Node Black e l1 l2, es2)
            _ -> error "Cannot happen"
      | otherwise =
          case go False n' es of
            (l1, e : es1) ->
              let (l2, es2) = go b n' es1
              in  (Node Black e l1 l2, es2)
            _ -> error "Cannot happen"
      where
        (n', r') = divMod n 2

toList :: Map2 k1 k2 -> [Entry k1 k2]
toList t = go t []
  where
    go Leaf r = r
    go (Node _ e l1 l2) r = go l1 (e : go l2 r)

instance (Ord2 k1, Eq2 k2) => Eq (Map2 k1 k2) where
  t1 == t2 = go (toList t1) (toList t2)
    where
      go :: (Ord2 k1, Eq2 k2) => [Entry k1 k2] -> [Entry k1 k2] -> Bool
      go [] [] = True
      go [] (_ : _) = False
      go (_ : _) [] = False
      go (Entry k1 v1 : es1) (Entry k2 v2 : es2) =
        case compare2 k1 k2 of
          EQ2 ->
            case eq2 v1 v2 of
              Just Refl -> go es1 es2
              _ -> False
          _ -> False

-- instance (Ord2 k1) => Container2 (Map2 k1) where
--   traverse2 _ Leaf = pure Leaf
--   traverse2 f (Node c (Entry y v) l1 l2) =
--     Node c <$> (Entry y <$> f v) <*> traverse2 f l1 <*> traverse2 f l2

--   zipWithA2 _f t1 t2 = fromAscList <$> (merge _f (toList t1) (toList t2))
--     where
--       merge :: (Ord2 k1, Applicative m) => (forall a. f a -> g a -> m (h a)) -> [Entry k1 f] -> [Entry k1 g] -> m [Entry k1 h]
--       merge _ [] _ = pure []
--       merge _ (_ : _) [] = pure []
--       merge f x@(Entry k1 v1 : es1) y@(Entry k2 v2 : es2) =
--         case compare2 k1 k2 of
--           LT2 -> merge f es1 y
--           GT2 -> merge f x es2
--           EQ2 -> (:) <$> (Entry k1 <$> f v1 v2) <*> merge f es1 es2
