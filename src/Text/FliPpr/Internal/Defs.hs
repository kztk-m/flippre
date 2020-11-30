{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Text.FliPpr.Internal.Defs where

import Control.Applicative (Alternative (..))
import Data.Kind (Type)
import Data.Typeable ((:~:) (..))
import qualified Text.FliPpr.Doc as D

-- | A type for (mutually recursive) definitions
data DType ft
  = -- | Type lifted from @ft@
    T ft
  | -- | Expressions that may share some definitions
    DType ft :*: DType ft

infixr 4 :*:

data DTypeVal (f :: ft -> Type) :: DType ft -> Type where
  VT :: f ft -> DTypeVal f (T ft)
  VProd :: DTypeVal f a -> DTypeVal f b -> DTypeVal f (a :*: b)

class Defs (exp :: k -> Type) | exp -> k where
  data Rules exp :: DType k -> Type

  -- By kztk @ 2020-11-26
  -- We will use the following methods for recursive definitions
  lift :: exp a -> Rules exp (T a)
  unlift :: Rules exp (T a) -> exp a

  pairRules :: Rules exp a -> Rules exp b -> Rules exp (a :*: b)
  unpairRules :: (DefType a, DefType b) => Rules exp (a :*: b) -> (Rules exp a -> Rules exp b -> Rules exp r) -> Rules exp r

  -- A method inspired by the trace operator in category theory.
  -- This method serves as a bulding block of mutual recursions
  letr :: (exp a -> Rules exp (T a :*: r)) -> Rules exp r

-- | A variant of 'many' defined without Haskell-level recursion.
manyD :: (Defs exp, Alternative exp) => exp a -> exp [a]
manyD d = unlift $ letr $ \a -> pairRules (lift $ pure [] <|> (:) <$> d <*> a) (lift a)

-- | A variant of 'some' defined without Haskell-level recursion.
someD :: (Defs exp, Alternative exp) => exp a -> exp [a]
someD d = unlift $ letr $ \a -> pairRules (lift d) $ lift $ (:) <$> a <*> manyD a

type family TransD f a = b | b -> a f where
  TransD f (T a) = T (f a)
  TransD f (a :*: b) = TransD f a :*: TransD f b

class DefType (a :: DType k) where
  indDType ::
    forall f.
    (forall a. f (T a)) ->
    (forall a b. (DefType a, DefType b) => f (a :*: b)) ->
    f a

instance DefType (T a) where
  indDType f _ = f

instance (DefType a, DefType b) => DefType (a :*: b) where
  indDType _ step = step

newtype PropTransD f a = PropTransD (Wit (DefType (TransD f a)))

data Wit c where
  Wit :: c => Wit c

propTransDPreservesDefType :: forall a f. DefType a => Wit (DefType (TransD f a))
propTransDPreservesDefType = let PropTransD k = indDType p0 pstep in k
  where
    p0 :: forall t. PropTransD f (T t)
    p0 = PropTransD Wit

    pstep :: forall aa bb. (DefType aa, DefType bb) => PropTransD f (aa :*: bb)
    pstep = case propTransDPreservesDefType @aa @f of
      Wit -> case propTransDPreservesDefType @bb @f of
        Wit -> PropTransD Wit

newtype InvDType f aa = InvDType (forall a b. aa :~: (a :*: b) -> (DefType a => DefType b => f a b) -> f a b)

invDType :: DefType (a :*: b) => (DefType a => DefType b => f a b) -> f a b
invDType =
  let InvDType k = indDType inv0 invStep in k Refl
  where
    inv0 :: InvDType f (T t)
    inv0 = InvDType $ \refl _ -> case refl of

    invStep :: (DefType aa, DefType bb) => InvDType f (aa :*: bb)
    invStep = InvDType $ \refl k -> case refl of
      Refl -> k

newtype LetRGen exp a = LetRGen (forall r. DefType r => (Rules exp a -> Rules exp (a :*: r)) -> Rules exp r)

letrGen :: (Defs exp, DefType a, DefType r) => (Rules exp a -> Rules exp (a :*: r)) -> Rules exp r
letrGen =
  let LetRGen f = indDType letrGen0 letrGenStep
   in f
  where
    letrGen0 :: Defs exp => LetRGen exp (T t)
    letrGen0 = LetRGen $ \h -> letr (h . lift)

    letrGenStep :: (DefType a, DefType b, Defs exp) => LetRGen exp (a :*: b)
    letrGenStep = LetRGen $ \h -> letrGen $ \b -> letrGen $ \a -> assocr (h (pairRules a b))
      where
        assocr :: (Defs exp, DefType a, DefType b, DefType r) => Rules exp ((a :*: b) :*: r) -> Rules exp (a :*: (b :*: r))
        assocr x =
          unpairRules x $ \ab c ->
            unpairRules ab $ \a b ->
              pairRules a (pairRules b c)

newtype RMap exp f g a = RMap ((forall t. exp (f t) -> exp (g t)) -> Rules exp (TransD f a) -> Rules exp (TransD g a))

rmap :: forall a exp f g. (DefType a, Defs exp) => (forall a. exp (f a) -> exp (g a)) -> Rules exp (TransD f a) -> Rules exp (TransD g a)
rmap =
  let RMap f = indDType rmap0 rmapStep in f
  where
    rmap0 :: Defs exp => RMap exp f g (T t)
    rmap0 = RMap $ \f -> lift . f . unlift

    rmapStep :: forall a b exp. (Defs exp, DefType a, DefType b) => RMap exp f g (a :*: b)
    rmapStep = RMap $ \f ab ->
      case propTransDPreservesDefType @a @f of
        Wit -> case propTransDPreservesDefType @b @f of
          Wit -> unpairRules ab $ \a b -> pairRules (rmap f a) (rmap f b)

shareDef :: (DefType a, DefType r, Defs exp) => Rules exp a -> (Rules exp a -> Rules exp r) -> Rules exp r
shareDef a h = letrGen (pairRules a . h)

fixDef :: (DefType a, Defs exp) => (Rules exp a -> Rules exp a) -> Rules exp a
fixDef h = letrGen $ \x -> pairRules (h x) x

-- | 'DefM' is a monad to make definitions easily.
--   We intentionally do not make it an instance of 'MonadFix'.

-- In implementation, it is a specialized version of a codensity monad.
newtype DefM exp a = DefM {unDefM :: forall r. DefType r => (a -> Rules exp r) -> Rules exp r}

instance Functor (DefM exp) where
  fmap f m = DefM $ \k -> unDefM m (k . f)

instance Applicative (DefM exp) where
  pure a = DefM $ \k -> k a
  a <*> b = DefM $ \k -> unDefM a $ \av -> unDefM b $ \bv -> k (av bv)

instance Monad (DefM exp) where
  return = pure
  m >>= f = DefM $ \k -> unDefM m $ \v -> unDefM (f v) k

runDefM :: DefType r => DefM exp (Rules exp r) -> Rules exp r
runDefM m = unDefM m id

unpairRulesM :: (Defs exp, DefType a, DefType b) => Rules exp (a :*: b) -> DefM exp (Rules exp a, Rules exp b)
unpairRulesM r = DefM $ \k -> unpairRules r $ curry k

class DefType a => Convertible exp a b | b -> a, b -> exp where
  fromRules :: Rules exp a -> DefM exp b
  toRules :: b -> Rules exp a

mfixDefM :: (Defs exp, Convertible exp a s) => (s -> DefM exp s) -> DefM exp s
mfixDefM h =
  fromRules $ fixDef (\a -> unDefM (fromRules a >>= h) toRules)

-- | 'share's computation.
share :: Defs exp => exp a -> DefM exp (exp a)
share s = DefM $ \k -> shareDef (lift s) $ \a -> k (unlift a)

shareGen :: forall exp a s. (Defs exp, DefType a, Convertible exp a s) => s -> DefM exp s
shareGen s = DefM $ \k -> shareDef (toRules @exp @a @s s) $ \a -> unDefM (fromRules @exp @a @s a) k

rule :: Defs exp => exp a -> DefM exp (Rules exp (T a))
rule = shareGen . lift

nt :: Defs exp => Rules exp (T a) -> exp a
nt = unlift

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

-- | Monads for managing variable names
class Monad m => VarM m where
  -- | A new variable name, which may or may not differ in calls.
  --   For de Bruijn levels, use the Reader monad and define
  --
  --   @
  --      newVar = do {i <- ask ; return ("x" ++ show i ) }
  --   @
  --
  --   Just for using different names, use the State monad and define
  --   @
  --      newVar = do { i <- get ; put (i + 1) ; return ("x" ++ show i) }
  --   @
  --
  --   This representation does not cover de Bruijn indices; we do not support them.
  newVar :: m String

  -- | +1 to the nesting level. This is just identity if ones to assign different names for different variables.
  nestScope :: m a -> m a

newtype PprDefs m _a = PprDefs {pprDefs :: D.Precedence -> m D.Doc}

data RPairD = RPairD D.Doc D.Doc | ROtherD D.Doc

pprRPairD :: RPairD -> D.Doc
pprRPairD (RPairD d1 d2) = D.hcat [D.text "<", D.align d1 D.<$$> D.text ",", D.align d2, D.text ">"]
pprRPairD (ROtherD d) = d

instance VarM m => Defs (PprDefs m) where
  newtype Rules (PprDefs m) _a = PRules {runPRules :: D.Precedence -> m RPairD}

  lift a = PRules $ \k -> do
    d <- pprDefs a 10
    return $ ROtherD $ D.parensIf (k > 9) $ D.text "↑" D.<> D.align d

  unlift r = PprDefs $ \k -> do
    d <- pprRPairD <$> runPRules r 10
    return $ D.parensIf (k > 9) $ D.text "↓" D.<> D.align d

  pairRules r1 r2 = PRules $ \_ -> do
    d1 <- pprRPairD <$> runPRules r1 0
    d2 <- pprRPairD <$> runPRules r2 0
    return $ RPairD d1 d2

  unpairRules m f = PRules $ \k -> do
    d <- pprRPairD <$> runPRules m 0
    x <- newVar
    y <- newVar
    dr <- nestScope $ nestScope $ pprRPairD <$> runPRules (f (PRules $ const $ return $ ROtherD $ D.text x) (PRules $ const $ return $ ROtherD $ D.text y)) 0
    return $
      ROtherD $
        D.parensIf (k > 0) $
          D.align $
            D.group $
              D.hsep [D.text "let", D.text "<" <> D.text x <> D.text "," D.<+> D.text y <> D.text ">", D.text "=", D.align d, D.text "in"]
                D.</> D.align dr

  letr f = PRules $ \k -> do
    x <- newVar
    res <- nestScope $ runPRules (f (PprDefs $ \_ -> return $ D.text x)) 0
    return $
      ROtherD $
        D.parensIf (k > 0) $ case res of
          RPairD d1 d2 ->
            D.align $
              D.group $
                D.hsep [D.text "let rec", D.text x, D.text "=", D.align d1, D.text "in"]
                  D.</> D.align d2
          ROtherD d ->
            D.align $ D.group $ D.text "letr" D.<+> D.text x <> D.text "." D.</> D.nest 2 (D.align d)
