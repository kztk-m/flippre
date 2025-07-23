{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Core Syntax
module Text.FliPpr.Internal.Core (
  -- * FliPpr Types
  FType (..),
  type (~>),
  D,
  FliPpr (..),

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
  In,

  -- * Conversion from/to Haskell functions
  Repr (..),
) where

import Data.Kind (Constraint, Type)
import qualified Data.RangeSet.List as RS
import Data.Typeable (Typeable)

import Control.Arrow (first)
import Data.Function.Compat (applyWhen)
import Data.String (IsString)
import Data.String.Compat (IsString (..))
import Debug.Trace (trace)
import qualified Defs as D
import GHC.Stack (CallStack)
import qualified Prettyprinter as PP
import qualified Text.FliPpr.Doc as DD

data NullaryOp = Abort CallStack | Space | Spaces | Line | LineBreak | Line' | NESpaces' | Text !String deriving stock Show
data UnaryOp = Align | Group | Nest !Int deriving stock Show
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

type family FVar v :: FType -> Type
data family In v :: Type -> Type
data Exp (s :: Phase) v a where
  Lam :: (In v a -> Exp s v b) -> Exp s v (a ~> b)
  App :: Exp s v (a ~> b) -> In v a -> Exp s v b
  Case :: CallStack -> In v a -> [Branch (In v) (Exp s v) a t] -> Exp s v t
  UnPair :: CallStack -> In v (a, b) -> (In v a -> In v b -> Exp s v t) -> Exp s v t
  UnUnit :: In v () -> Exp s v a -> Exp s v a
  CharAs :: In v Char -> RS.RSet Char -> Exp s v D
  Op0 :: !NullaryOp -> Exp s v D
  Op1 :: !UnaryOp -> Exp s v D -> Exp s v D
  Op2 :: !BinaryOp -> Exp s v D -> Exp s v D -> Exp s v D
  Var :: FVar v a -> Exp s v a
  Local :: Def s v '[] a -> Exp s v a

-- | A newtype wrapper for the FliPpr expression type: @forall v. Exp s v a@.
newtype FliPpr s a = FliPpr (forall v. Exp s v a)

instance (D ~ t) => Semigroup (Exp s v t) where
  (<>) x y = Op2 Cat x (Op2 Cat (Op0 Spaces) y)

instance (D ~ t) => IsString (Exp s v t) where
  fromString = Op0 . Text

instance (D ~ t) => DD.DocLike (Exp s v t) where
  empty = Op0 (Text "")
  x <+> y = x <#> Op0 Space <#> Op0 Spaces <#> y
    where
      (<#>) = Op2 Cat

  line = Op0 Line
  linebreak = Op0 LineBreak

  align = Op1 Align
  nest = Op1 . Nest
  group = Op1 Group

-- TODO: Use it only for the explicit syntax. The implicit syntax should use
-- tying knot instead.

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

-- |
-- The type class 'Repr' provides the two method 'toFunction' and 'fromFunction', which
-- perform interconversion between FliPpr functions and Haskell functions.
class Repr s v (t :: FType) r | r -> t s v where
  toFunction :: Exp s v t -> r
  -- ^ @toFunction :: Exp s v (a1 ~> ... ~> an ~> D) -> v a1 -> ... -> v an -> Exp s v D@

  fromFunction :: r -> Exp s v t
  -- ^ @fromFunction :: (v a1 -> ... -> v an -> Exp s v D) -> Exp s v (a1 ~> ... ~> an ~> D)@

instance Repr s v t (Exp s v t) where
  toFunction = id
  fromFunction = id

instance (Repr s v t r) => Repr s v (a ~> t) (In v a -> r) where
  toFunction f a = toFunction (f `App` a)
  fromFunction k = Lam (fromFunction . k)

instance D.Arg (Exp s v) (Exp s v a) where
  letr f = D.letr $ fmap (first D.Tip) . f . D.unTip

-- One-level unfolding to avoid overlapping instances.
instance (Repr s v t r) => D.Arg (Exp s v) (In v a -> r) where
  letr f = D.letr $ fmap (first fromFunction) . f . toFunction

data ToPrint

newtype instance In ToPrint a = DLevel Int
newtype FLevel (a :: FType) = FLevel Int
type instance FVar ToPrint = FLevel

pprIn :: Int -> PP.Doc ann
pprIn i = fromString "x_" <> PP.viaShow i

pprFVar :: Int -> PP.Doc ann
pprFVar i = fromString "f_" <> PP.viaShow i

ppr :: Int -> Int -> Int -> Exp s ToPrint a -> PP.Doc ann
ppr dlevel flevel k e0 = case e0 of
  Lam h ->
    let vn = DLevel dlevel
        d = ppr (dlevel + 1) flevel 0 (h vn)
    in  applyWhen (k > 0) PP.parens $
          PP.fillSep [fromString "\\" <> pprIn dlevel PP.<+> fromString "->", d]
  App e (DLevel n) ->
    applyWhen (k > 9) PP.parens $
      ppr dlevel flevel 9 e PP.<+> pprIn n
  Case _ (DLevel x) brs ->
    let sep x y = PP.fillSep [x <> fromString ",", y]
        pprBr (Branch (PartialBij s _ _) h) =
          let vn = DLevel dlevel
          in  PP.group $
                PP.nest 2 $
                  PP.sep
                    [ PP.hsep [fromString s, fromString "$", fromString "\\" <> pprIn dlevel, fromString "->"]
                    , ppr (dlevel + 1) flevel 0 (h vn)
                    ]
        ds = map pprBr brs
    in  applyWhen (k > 9) PP.parens $
          fromString "case_"
            PP.<+> pprIn x
            PP.<+> PP.brackets (PP.align $ PP.concatWith sep ds)
  UnPair _ (DLevel x) h ->
    let vn1 = DLevel dlevel
        vn2 = DLevel (dlevel + 1)
        dx = pprIn x
        dh = ppr (dlevel + 2) flevel 0 (h vn1 vn2)
    in  applyWhen (k > 0) PP.parens $
          PP.align $
            PP.group $
              PP.fillSep
                [ PP.hsep
                    [ fromString "let"
                    , PP.parens (pprIn dlevel <> fromString "," <> pprIn (dlevel + 1))
                    , fromString "="
                    , PP.align dx
                    ]
                , fromString "in" PP.<+> PP.align dh
                ]
  UnUnit (DLevel x) e ->
    let dx = pprIn x
        de = ppr dlevel flevel 0 e
    in  applyWhen (k > 0) PP.parens $
          PP.align $
            PP.group $
              PP.fillSep
                [ PP.hsep [fromString "let () =", PP.align dx]
                , PP.hsep [fromString "in", PP.align de]
                ]
  CharAs (DLevel x) rs ->
    applyWhen (k > 9) PP.parens $
      PP.hsep [pprIn x, fromString "`charAs`", PP.viaShow rs]
  Var (FLevel x) -> pprFVar x
  Op0 op -> case op of
    Line -> fromString "line"
    Abort _ -> fromString "abort"
    Space -> fromString "space"
    Spaces -> fromString "spaces"
    LineBreak -> fromString "lineBreak"
    Line' -> fromString "line'"
    NESpaces' -> fromString "nespaces'"
    Text s -> applyWhen (k > 9) PP.parens $ PP.hsep [fromString "text", PP.viaShow s]
  Op1 op e ->
    let d = ppr dlevel flevel 10 e
        fn = case op of
          Nest i -> PP.hsep [fromString "nest", PP.pretty i]
          Group -> fromString "group"
          Align -> fromString "align"
    in  applyWhen (k > 9) PP.parens $ PP.nest 2 $ PP.sep [fn, PP.align d]
  Op2 Cat e1 e2 ->
    let d1 = ppr dlevel flevel 5 e1
        d2 = ppr dlevel flevel 5 e2
    in  applyWhen (k > 5) PP.parens $ PP.group $ PP.fillSep [d1, fromString "<#>" PP.<+> PP.align d2]
  Op2 BChoice e1 e2 ->
    let d1 = ppr dlevel flevel 4 e1
        d2 = ppr dlevel flevel 4 e2
    in  applyWhen (k > 4) PP.parens $ PP.group $ PP.fillSep [d1, fromString "<?" PP.<+> PP.align d2]
  Local d ->
    applyWhen (k > 9) PP.parens $
      PP.group $
        PP.align $
          PP.nest 2 $
            PP.sep [fromString "local", pprDef dlevel flevel 10 d]

pprDef :: Int -> Int -> Int -> Def s ToPrint as a -> PP.Doc ann
pprDef dlevel flevel k d0 = case d0 of
  DefRet e ->
    applyWhen (k > 9) PP.parens $
      PP.group $
        PP.align $
          PP.sep [fromString "ret", ppr dlevel flevel 10 e]
  DefCons e d ->
    applyWhen (k > 1) PP.parens $
      PP.group $
        PP.align $
          PP.sep
            [ ppr dlevel flevel 3 e
            , fromString "#" PP.<+> pprDef dlevel flevel 2 d
            ]
  DefLetr h ->
    let fn = FLevel flevel
        d = pprDef dlevel (flevel + 1) 0 (h fn)
    in  applyWhen (k > 0) PP.parens $
          PP.group $
            PP.align $
              PP.angles $
                PP.hsep
                  [ fromString "let"
                  , pprFVar flevel
                  , fromString "# ___"
                  , fromString "="
                  , d
                  ]

instance (ToPrint ~ v) => PP.Pretty (Exp Explicit v a) where
  pretty = ppr 0 0 0

instance (ToPrint ~ v) => Show (Exp Explicit v a) where
  showsPrec k e = shows (ppr 0 0 k e)

instance Show (FliPpr Explicit a) where
  showsPrec k (FliPpr e) = showsPrec k e