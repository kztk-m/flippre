{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | Core Syntax
module Text.FliPpr.Internal.Core (
  -- * FliPpr Types
  FType (..),
  type (~>),
  D,

  -- * FliPpr Expressions and Definitions
  NullaryOp (..),
  UnaryOp (..),
  BinaryOp (..),
  PartialBij (..),
  Branch (..),
  Exp (..),
  Def (..),
  Phase (..),
  FVar,
) where

import Data.Kind (Constraint, Type)
import qualified Data.RangeSet.List as RS
import Data.Typeable (Typeable)

import qualified Defs as D

data NullaryOp = Abort | Space | Spaces | Line | LineBreak | Line' | NESpaces' | Text !String deriving stock Show
data UnaryOp = Align | Group | Next !Int deriving stock Show
data BinaryOp = Cat | BChoice deriving stock Show

-- | The kind for FliPpr types.
data FType = FTypeD | Type :~> FType

-- | Unticked synonym for :~> used for readability.
type a ~> b = a :~> b

infixr 0 ~>
infixr 0 :~>

-- | Unticked synonym for FTypeD
type D = 'FTypeD

-- | Partial bijections between @a@ and @b@.
data PartialBij a b
  = PartialBij
      !String
      -- ^ field used for pretty-printing
      !(a -> Maybe b)
      -- ^ forward transformation
      !(b -> Maybe a)
      -- ^ backward transformation

-- | A datatype represents branches.
data Branch arg exp a (t :: FType)
  = -- | the part @arg b -> exp t@ must be a linear function
    forall b. Branch (PartialBij a b) (arg b -> exp t)

data Phase = Implicit | Explicit

type family ConstraintFType (t :: Phase) (a :: FType) :: Constraint where
  ConstraintFType Implicit a = Typeable a
  ConstraintFType Explicit a = ()

type family ConstraintType (t :: Phase) (a :: Type) :: Constraint where
  ConstraintType Implicit a = Typeable a
  ConstraintType Explicit a = ()

type family FVar (v :: Type -> Type) :: FType -> Type

data Exp (s :: Phase) v a where
  Lam :: (v a -> Exp s v b) -> Exp s v (a ~> b)
  App :: Exp s v (a ~> b) -> v a -> Exp s v b
  Case :: v a -> [Branch v (Exp s v) a t] -> Exp s v t
  UnPair :: v (a, b) -> (v a -> v b -> Exp s v t) -> Exp s v t
  UnUnit :: v () -> Exp s v a -> Exp s v a
  CharAs :: v Char -> RS.RSet Char -> Exp s v D
  Op0 :: !NullaryOp -> Exp s v D
  Op1 :: !UnaryOp -> Exp s v D -> Exp s v D
  Op2 :: !BinaryOp -> Exp s v D -> Exp s v D -> Exp s v D
  Var :: FVar v a -> Exp s v a
  Local :: Def s v '[] a -> Exp s v a

data Def s v as a where
  DefRet :: Exp s v r -> Def s v '[] r
  DefCons :: Exp s v a -> Def s v as r -> Def s v (a : as) r
  DefLetr :: (FVar v a -> Def s v (a : as) r) -> Def s v as r

instance D.Defs (Exp s v) where
  newtype D (Exp s v) as r = DExp {unDCoreExp :: Def s v as r}
  liftD = DExp . DefRet
  consD e (DExp ds) = DExp $ DefCons e ds
  unliftD (DExp ds) = Local ds
  letrD h = DExp $ DefLetr (unDCoreExp . h . Var)
