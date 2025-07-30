{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

-- | Core Syntax
module Text.FliPpr.Internal.Core (
  -- * FliPpr Types
  FType (..),
  type (~>),
  D,
  FliPpr (..),
  flippr,
  FliPprM,
  Phased (..),
  SPhase (..),

  -- * FliPpr Expressions and Definitions
  NullaryOp (..),
  UnaryOp (..),
  BinaryOp (..),
  PartialBij (..),
  Branch (..),
  Exp (..),
  ExpsI (..),
  Def (..),
  Phase (..),
  FVar,
  In,

  -- * Conversion from/to Haskell functions
  Repr (..),
) where

import Data.Kind (Type)
import qualified Data.RangeSet.List as RS

-- import Data.Typeable (Typeable)

import Control.Arrow (first)
import Data.Coerce (coerce)
import Data.Function.Compat (applyWhen)
import Data.String (IsString)
import Data.String.Compat (IsString (..))
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

data SPhase s where
  SImplicit :: SPhase Implicit
  SExplicit :: SPhase Explicit

class Phased s where
  phase :: SPhase s

instance Phased Implicit where
  phase = SImplicit

instance Phased Explicit where
  phase = SExplicit

-- type family ConstraintFType (t :: Phase) (a :: FType) :: Constraint where
--   ConstraintFType Implicit a = Typeable a
--   ConstraintFType Explicit a = ()

-- type family ConstraintType (t :: Phase) (a :: Type) :: Constraint where
--   ConstraintType Implicit a = Typeable a
--   ConstraintType Explicit a = ()

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

-- | Make a closed FliPpr definition. A typical use is:
--
--   > flippr $ do
--   >   rec ppr <- share $ arg $ \i -> ...
--   >   return ppr
flippr :: (forall v. FliPprM s v (Exp s v a)) -> FliPpr s a
flippr x = FliPpr (localSp x)
  where
    localSp :: D.DefM (Exp s v) (Exp s v a) -> Exp s v a
    localSp (D.DefM r) =
      Local (coerce r DefRet)

type FliPprM s v = D.DefM (Exp s v)

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
  DefLetr :: (FVar v a -> Def Explicit v (a : as) r) -> Def Explicit v as r

data ExpsI v as where
  ExpNil :: ExpsI v '[]
  ExpCons :: Exp Implicit v a -> ExpsI v as -> ExpsI v (a : as)
instance (Phased s) => D.Defs (Exp s v) where
  newtype D (Exp s v) as r = DExp {unDCoreExp :: Def s v as r}
  liftD e = DExp $ DefRet e
  consD e (DExp ds) = DExp $ DefCons e ds
  unliftD (DExp ds) = Local ds
  letrD h = DExp $ case phase @s of
    SExplicit -> DefLetr (\x -> unDCoreExp (h $ Var x))
    SImplicit ->
      let DefCons e ds = unDCoreExp (h e)
      in  ds

-- |
-- The type class 'Repr' provides the two method 'toFunction' and 'fromFunction', which
-- perform interconversion between FliPpr functions and Haskell functions.
class Repr s v r | r -> s v where
  type ReprT r :: FType

  toFunction :: Exp s v (ReprT r) -> r
  -- ^ @toFunction :: Exp s v (a1 ~> ... ~> an ~> D) -> v a1 -> ... -> v an -> Exp s v D@

  fromFunction :: r -> Exp s v (ReprT r)
  -- ^ @fromFunction :: (v a1 -> ... -> v an -> Exp s v D) -> Exp s v (a1 ~> ... ~> an ~> D)@

instance (s' ~ s) => Repr s' v (Exp s v t) where
  type ReprT (Exp s v t) = t
  toFunction = id
  fromFunction = id

instance (Repr s v r) => Repr s v (In v a -> r) where
  type ReprT (In v a -> r) = a ~> ReprT r
  toFunction f a = toFunction (f `App` a)
  fromFunction k = Lam (fromFunction . k)

instance (Phased s) => D.Arg (Exp s v) (Exp s v a) where
  letr f = D.letr $ fmap (first D.Tip) . f . D.unTip

-- One-level unfolding to avoid overlapping instances.
instance (v ~ v', Phased s, Repr s v r) => D.Arg (Exp s v') (In v a -> r) where
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
          PP.nest 2 $
            PP.sep
              [ PP.hcat [fromString "\\", pprIn dlevel] PP.<+> fromString "->"
              , d
              ]
  App e (DLevel n) ->
    applyWhen (k > 9) PP.parens $
      ppr dlevel flevel 9 e PP.<+> pprIn n
  Case _ (DLevel x) brs ->
    let pprBr (Branch (PartialBij s _ _) h) =
          let vn = DLevel dlevel
          in  PP.group $
                PP.nest 2 $
                  PP.sep
                    [ PP.hsep [fromString s, fromString "$", fromString "\\" <> pprIn dlevel, fromString "->"]
                    , ppr (dlevel + 1) flevel 0 (h vn)
                    ]
        ds = map (PP.align . pprBr) brs
    in  applyWhen (k > 9) PP.parens $
          fromString "case_"
            PP.<+> pprIn x
            PP.<+> PP.align (PP.list ds)
  UnPair _ (DLevel x) h ->
    let vn1 = DLevel dlevel
        vn2 = DLevel (dlevel + 1)
        dx = pprIn x
        dh = ppr (dlevel + 2) flevel 0 (h vn1 vn2)
    in  applyWhen (k > 0) PP.parens $
          PP.align $
            PP.group $
              PP.sep
                [ PP.hsep
                    [ fromString "let"
                    , PP.parens (pprIn dlevel <> fromString "," <> pprIn (dlevel + 1))
                    , fromString "="
                    , PP.align dx
                    , fromString "in"
                    ]
                , PP.align dh
                ]
  UnUnit (DLevel x) e ->
    let dx = pprIn x
        de = ppr dlevel flevel 0 e
    in  applyWhen (k > 0) PP.parens $
          PP.align $
            PP.group $
              PP.sep
                [ PP.hsep [fromString "let () =", PP.align dx, fromString "in"]
                , PP.hsep [PP.align de]
                ]
  CharAs (DLevel x) rs ->
    applyWhen (k > 9) PP.parens $
      PP.hsep [pprIn x, fromString "`charAs`", pprRangeSet rs]
  Var (FLevel x) -> pprFVar x
  Op0 op -> case op of
    Line -> fromString "line"
    Abort _ -> fromString "abort"
    Space -> fromString "space"
    Spaces -> fromString "spaces"
    LineBreak -> fromString "lineBreak"
    Line' -> fromString "line'"
    NESpaces' -> fromString "nespaces'"
    Text s -> applyWhen (k > 9) PP.parens $ PP.sep [fromString "text", PP.viaShow s]
  Op1 op e ->
    let d = ppr dlevel flevel 10 e
        fn = case op of
          Nest i -> PP.hsep [fromString "nest", PP.pretty i]
          Group -> fromString "group"
          Align -> fromString "align"
    in  applyWhen (k > 9) PP.parens $ PP.nest 2 $ PP.sep [fn, PP.align d]
  Op2 Cat e1 (gatherCats -> es) ->
    case es of
      [e2] ->
        let d1 = ppr dlevel flevel 6 e1
            d2 = ppr dlevel flevel 5 e2
        in  applyWhen (k > 5) PP.parens $ PP.group $ PP.sep [d1, fromString "<#>" PP.<+> PP.align d2]
      _ ->
        let ds = map (PP.align . ppr dlevel flevel 0) (e1 : es)
        in  applyWhen (k > 9) PP.parens $
              PP.group $
                PP.nest 2 $
                  PP.sep [fromString "hcat", PP.align $ PP.list ds]
  Op2 BChoice e1 e2 ->
    let d1 = ppr dlevel flevel 4 e1
        d2 = ppr dlevel flevel 4 e2
    in  applyWhen (k > 4) PP.parens $ PP.group $ PP.sep [d1, fromString "<?" PP.<+> PP.align d2]
  Local (gatherLetRec flevel -> (xs, ds0, dr)) ->
    let ds = reverse ds0
        dbody
          | [x] <- xs
          , [d] <- ds0 =
              PP.vsep
                [ PP.hsep
                    [ fromString "let"
                    , pprFVar x
                    , fromString "="
                    , PP.align d
                    , fromString "in"
                    ]
                , PP.align dr
                ]
          | otherwise =
              PP.vsep
                [ PP.nest 2 $
                    PP.vsep
                      [ fromString "let"
                      , PP.concatWith (\x y -> x <> PP.hardline <> y) [PP.hsep [pprFVar x, fromString "=", PP.align d] | (x, d) <- zip xs ds]
                      ]
                , PP.hsep [fromString "in", PP.align dr]
                ]
    in  applyWhen (k > 0) PP.parens $ PP.align $ PP.group dbody
    -- Local d ->
    --   applyWhen (k > 9) PP.parens $
    --     PP.group $
    --       PP.align $
    --         PP.nest 2 $
    --           PP.sep [fromString "local", pprDef dlevel flevel 10 d]
  where
    pprRangeSet :: (Show a, Enum a, Bounded a, Eq a) => RS.RSet a -> PP.Doc ann
    pprRangeSet rs
      | RS.null rs = fromString "empty"
      | RS.isFull rs = fromString "full"
      | [c] <- RS.toList rs = PP.hsep [fromString "singleton", PP.viaShow c]
      | otherwise = PP.viaShow rs

    gatherCats :: Exp s ToPrint D -> [Exp s ToPrint D]
    gatherCats (Op2 Cat e1 e2) = e1 : gatherCats e2
    gatherCats e = [e]

    gatherLetRec :: Int -> Def s ToPrint as a -> ([Int], [PP.Doc ann], PP.Doc ann)
    gatherLetRec fl (DefRet e) = ([], [], ppr dlevel fl 0 e)
    gatherLetRec fl (DefCons e def) =
      let d = ppr dlevel fl 0 e
          (xs, ds, dr) = gatherLetRec fl def
      in  (xs, d : ds, dr)
    gatherLetRec fl (DefLetr h) =
      let fn = FLevel fl
          (xs, ds, dr) = gatherLetRec (fl + 1) (h fn)
      in  (fl : xs, ds, dr)

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
                  [ fromString "letr"
                  , pprFVar flevel
                  , fromString "."
                  , d
                  ]

--  DefI (_, _) -> error "We cannot print implicit expressions as they may have cycles."

instance (ToPrint ~ v) => PP.Pretty (Exp Explicit v a) where
  pretty = ppr 0 0 0

instance (ToPrint ~ v) => Show (Exp Explicit v a) where
  showsPrec k e = shows (ppr 0 0 k e)

instance Show (FliPpr Explicit a) where
  showsPrec k (FliPpr e) = showsPrec k e