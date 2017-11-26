{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

{-|
This module provides the type class 'Fix' that extends a fixpoint operator for
some specific domain to more domains by using Bekic's lemma. 

@@
data DD a = DFix (a -> DD a) | DVar a | DBr String [DD a]

instance Fix (DD a) where
  fix f = DFix (f . DVar)

instance (a ~ String) => Show (DD a) where
  show x = go x 0
    where
      varName k = "x" ++ show k
      
      go (DVar s)  k      = s
      go (DFix f)  k      = "(μ" ++ varName k ++ ". " ++ go (f (varName k)) (k+1) ++ ")"
      go (DBr s es) k     = show s ++ "[" ++ goList es ++ "]"
        where
          goList []  = ""
          goList [e] = go e k
          goList (e:es) = go e k ++ ", " ++ goList es


test1 :: Int -> DD a 
test1 =
  nfix $ \z i ->
     if i == 0 then DBr "a" [ z 1, z 2, z 3 ]
     else if i == 1 then DBr "a" [ z 4 ]
     else if i == 2 then DBr "b" [ z 4 ]
     else if i == 3 then DBr "c" [ z 3 ]
     else                DBr "d" []
@@

>>> test1 0
(μx0. "a"[(μx1. "a"[(μx2. "d"[])]), (μx1. "b"[(μx2. "d"[])]), (μx1. "c"[x1])])


-}

module Text.FliPpr.Fix
  ( Fix(..)
  , nfix
  , End
  , (:>)(..) ) where 

import qualified Data.Map as M 
import Data.Typeable 

class Fix a where
  fix :: (a -> a) -> a

instance Fix () where
  fix _ = ()

{-
Bekic's Lemma
-}
instance (Fix a, Fix b) => Fix (a,b) where
  fix f = 
    (fix (\z -> fst (f (z, fix (\w -> snd (f (z,w)))))),
     fix (\z -> snd (f (fix (\w -> fst (f (w,z))), z))))

instance (Fix a, Fix b, Fix c) => Fix (a,b,c) where
  fix f = from $ fix (to . f . from)
    where
      from ((a,b),c) = (a,b,c)
      to (a,b,c) = ((a,b),c)

instance (Fix a, Fix b, Fix c, Fix d) => Fix (a,b,c,d) where
  fix f = from $ fix (to . f . from)
    where
      from ((a,b),(c,d)) = (a,b,c,d)
      to (a,b,c,d) = ((a,b), (c,d))

-- | Finitenes of @k@ is needed to guarantee its termination.
instance (Bounded k, Ord k, Fix a) => Fix (k -> a) where
  fix = nfix 

-- | Slow? 
instance (Bounded k, Ord k, Enum k, Fix a) => Fix (M.Map k a) where
  fix f = toMap $ fix (fromMap . f . toMap)
    where
      keys = [minBound .. maxBound]
      toMap   h = M.fromAscList [ (k,h k) | k <- keys ]
      fromMap m = \k -> maybe undefined id (M.lookup k m)
    
nfix :: (Bounded k, Ord k, Fix a) => ((k -> a) -> (k -> a)) -> k -> a
nfix f = go M.empty 
  where
    go mp k = fix (\kv -> f (\i -> let mp' = M.insert k kv mp
                                   in maybe (go mp' i) id (M.lookup i mp')) k)

data End = End deriving (Eq, Ord, Bounded, Show, Typeable)
data a :> b = a :> b deriving (Eq, Ord, Bounded, Show, Typeable)

proj1 :: (a :> r) -> a
proj1 (a :> _) = a

proj2 :: (a :> b :> r) -> b
proj2 (_ :> a :> _) = a

proj3 :: (a :> b :> c :> r) -> c 
proj3 (_ :> _ :> a :> _) = a

proj4 :: (a :> b :> c :> d :> r) -> d 
proj4 (_ :> _ :> _ :> a :> _) = a 

infixr 0 :>

instance Fix End where
  fix _ = End

instance (Fix a, Fix b) => Fix (a :> b) where
  fix f = from (fix (to . f . from))
    where
      from (a,b)    = a :> b
      to   (a :> b) = (a,b) 



{- TODO:

Is it difficult to support the following way of writing programs?

fix $ \r ->
  Lab1 := ... r Labk ... r Labk'
  `add`
  (Lab2 := ... )
  `and`
  ... 

Here, r is some extensible records and Lab1 ... are labels for the record.
-}
