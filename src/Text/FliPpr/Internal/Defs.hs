{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Text.FliPpr.Internal.Defs where

import Data.Kind (Type)

-- | A type for (mutually recursive) definitions
data DType ft
  = -- | Type lifted from @ft@
    T ft
  | -- | Expressions that may share some definitions
    DType ft :*: DType ft

infixr 4 :*:

class Defs (exp :: k -> Type) | exp -> k where
  data Rules exp :: DType k -> Type

  -- By kztk @ 2020-11-26
  -- We will use the following methods for recursive definitions
  lift :: exp a -> Rules exp (T a)
  unlift :: Rules exp (T a) -> exp a

  pairRules :: Rules exp a -> Rules exp b -> Rules exp (a :*: b)
  unpairRules :: Rules exp (a :*: b) -> (Rules exp a -> Rules exp b -> Rules exp r) -> Rules exp r

  -- A method inspired by the trace operator in category theory.
  -- This method serves as a bulding block of mutual recursions
  letr :: (exp a -> Rules exp (T a :*: r)) -> Rules exp r

class DefType (a :: DType k) where
  letrGen :: Defs exp => (Rules exp a -> Rules exp (a :*: r)) -> Rules exp r

  shareDef :: Defs exp => Rules exp a -> (Rules exp a -> Rules exp r) -> Rules exp r
  shareDef a h = letrGen (pairRules a . h)

  fixDef :: Defs exp => (Rules exp a -> Rules exp a) -> Rules exp a
  fixDef h = letrGen $ \x -> pairRules (h x) x

instance DefType (T a) where
  letrGen h = letr (h . lift)

instance (DefType a, DefType b) => DefType (a :*: b) where
  letrGen h = letrGen $ \b -> letrGen $ \a -> assocr (h (pairRules a b))
    where
      assocr :: Defs exp => Rules exp ((a :*: b) :*: r) -> Rules exp (a :*: (b :*: r))
      assocr x =
        unpairRules x $ \ab c ->
          unpairRules ab $ \a b ->
            pairRules a (pairRules b c)

-- | 'DefM' is a monad to make definitions easily.
--   We intentionally do not make it an instance of 'MonadFix'.

-- In implementation, it is a specialized version of a codensity monad.
newtype DefM exp a = DefM {unDefM :: forall r. (a -> Rules exp r) -> Rules exp r}

instance Functor (DefM exp) where
  fmap f m = DefM $ \k -> unDefM m (k . f)

instance Applicative (DefM exp) where
  pure a = DefM $ \k -> k a
  a <*> b = DefM $ \k -> unDefM a $ \av -> unDefM b $ \bv -> k (av bv)

instance Monad (DefM exp) where
  return = pure
  m >>= f = DefM $ \k -> unDefM m $ \v -> unDefM (f v) k

runDefM :: DefM exp (Rules exp r) -> Rules exp r
runDefM m = unDefM m id

unpairRulesM :: Defs exp => Rules exp (a :*: b) -> DefM exp (Rules exp a, Rules exp b)
unpairRulesM r = DefM $ \k -> unpairRules r $ curry k

class DefType a => Convertible exp a b | b -> a, b -> exp where
  fromRules :: Rules exp a -> DefM exp b
  toRules :: b -> Rules exp a

mfixDefM :: (Defs exp, Convertible exp a s) => (s -> DefM exp s) -> DefM exp s
mfixDefM h =
  fromRules $ fixDef (\a -> unDefM (fromRules a >>= h) toRules)

-- | 'share's computation.
share :: (Defs exp, Convertible exp a s) => s -> DefM exp s
share s = DefM $ \k -> shareDef (toRules s) $ \a -> unDefM (fromRules a) k

local :: Defs exp => DefM exp (exp t) -> exp t
local m = unlift $ runDefM $ fmap lift m

instance DefType a => Convertible exp a (Rules exp a) where
  fromRules = return
  toRules = id

instance (Defs exp, Convertible exp a s, Convertible exp b t) => Convertible exp (a :*: b) (s, t) where
  fromRules ab = do
    (a, b) <- unpairRulesM ab
    (,) <$> fromRules a <*> fromRules b

  toRules (x, y) = pairRules (toRules x) (toRules y)

instance (Defs exp, Convertible exp a1 s1, Convertible exp a2 s2, Convertible exp a3 s3) => Convertible exp (a1 :*: a2 :*: a3) (s1, s2, s3) where
  fromRules a = do
    (s1, (s2, s3)) <- fromRules a
    return (s1, s2, s3)

  toRules (s1, s2, s3) = toRules (s1, (s2, s3))

instance (Defs exp, Convertible exp a1 s1, Convertible exp a2 s2, Convertible exp a3 s3, Convertible exp a4 s4) => Convertible exp (a1 :*: a2 :*: a3 :*: a4) (s1, s2, s3, s4) where
  fromRules a = do
    (s1, (s2, (s3, s4))) <- fromRules a
    return (s1, s2, s3, s4)

  toRules (s1, s2, s3, s4) = toRules (s1, (s2, (s3, s4)))

instance (Defs exp, Convertible exp a1 s1, Convertible exp a2 s2, Convertible exp a3 s3, Convertible exp a4 s4, Convertible exp a5 s5) => Convertible exp (a1 :*: a2 :*: a3 :*: a4 :*: a5) (s1, s2, s3, s4, s5) where
  fromRules a = do
    (s1, (s2, (s3, (s4, s5)))) <- fromRules a
    return (s1, s2, s3, s4, s5)

  toRules (s1, s2, s3, s4, s5) = toRules (s1, (s2, (s3, (s4, s5))))

instance
  (Defs exp, Convertible exp a1 s1, Convertible exp a2 s2, Convertible exp a3 s3, Convertible exp a4 s4, Convertible exp a5 s5, Convertible exp a6 s6) =>
  Convertible exp (a1 :*: a2 :*: a3 :*: a4 :*: a5 :*: a6) (s1, s2, s3, s4, s5, s6)
  where
  fromRules a = do
    (s1, (s2, (s3, (s4, (s5, s6))))) <- fromRules a
    return (s1, s2, s3, s4, s5, s6)

  toRules (s1, s2, s3, s4, s5, s6) = toRules (s1, (s2, (s3, (s4, (s5, s6)))))
