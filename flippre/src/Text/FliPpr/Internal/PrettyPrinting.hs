{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use newtype instead of data" #-}

module Text.FliPpr.Internal.PrettyPrinting (
  pprMode,
  pprModeMono,
  PrettyPrintingMode,
) where

import Data.Coerce (coerce)
import Text.FliPpr.Doc
import Text.FliPpr.Internal.Core

import qualified Data.RangeSet.List as RS

import GHC.Stack (prettyCallStack)
import Unembedding.Env (Env (ENil, (:.)))

data Ppr d (t :: FType) where
  PD :: !d -> Ppr d D
  PF :: !(a -> Ppr d r) -> Ppr d (a ~> r)

-- | A type level label for pretty-printing interpretation
data PrettyPrintingMode d

newtype instance In (PrettyPrintingMode d) a = InPpr a
type instance FVar (PrettyPrintingMode d) = Ppr d

pprInterp :: (DocLike d) => Exp s (PrettyPrintingMode d) a -> Ppr d a
pprInterp (Lam h) = PF (coerce (pprInterp . h))
pprInterp (App (pprInterp -> PF f) a) = f (coerce a)
pprInterp (Case _callStack x brs0) = go (coerce x) brs0
  where
    go _ [] =
      error $
        unlines ["Pattern matching failure", prettyCallStack _callStack]
    go a (Branch (PartialBij _ f _) h : brs) =
      case f a of
        Nothing -> go a brs
        Just b -> pprInterp $ h (InPpr b)
pprInterp (UnPair _callStack (InPpr (a, b)) h) = pprInterp (h (coerce a) (coerce b))
pprInterp (UnUnit _ e) = pprInterp e
pprInterp (CharAs (InPpr c) rs)
  | c `RS.member` rs = PD (text [c])
  | otherwise =
      error $
        unlines
          [ "charAs: Condition violated."
          , show c <> " is not a member of " <> show rs
          ]
pprInterp (Op0 (Abort cs)) =
  error $ unlines ["Abort called.", prettyCallStack cs]
pprInterp (Op0 Line) = PD line
pprInterp (Op0 Line') = PD line
pprInterp (Op0 LineBreak) = PD linebreak
pprInterp (Op0 Space) = PD (text " ")
pprInterp (Op0 NESpaces') = PD (text " ")
pprInterp (Op0 Spaces) = PD (text "")
pprInterp (Op0 (Text s)) = PD (text s)
pprInterp (Op1 (Nest i) (pprInterp -> PD d)) =
  PD $ nest i d
pprInterp (Op1 Group (pprInterp -> PD d)) =
  PD $ group d
pprInterp (Op1 Align (pprInterp -> PD d)) =
  PD $ align d
pprInterp (Op2 Cat (pprInterp -> PD d1) (pprInterp -> PD d2)) =
  PD $ d1 <> d2
pprInterp (Op2 BChoice (pprInterp -> PD d1) _) = PD d1
pprInterp (Var d) = d
pprInterp (Local def) = snd $ pprInterpD def

-- Env is strict, so we use constructor to introduce laziness.
data LazyPpr d t = LazyPpr {forcePpr :: Ppr d t}

pprInterpD :: (DocLike d) => Def s (PrettyPrintingMode d) as r -> (Env (LazyPpr d) as, Ppr d r)
pprInterpD (DefRet e) = (ENil, pprInterp e)
pprInterpD (DefCons (pprInterp -> d) (pprInterpD -> (defs, dr))) =
  (LazyPpr d :. defs, dr)
pprInterpD (DefLetr h) =
  let ~(x :. defs, dr) = pprInterpD $ h (forcePpr x)
  in  (defs, dr)

-- instance (DocLike d) => FliPprE Identity (Ppr d) where
--   fapp (PF f) a = f (coerce a)

--   farg f = PF (coerce f)

--   fcase e0 = go (coerce e0)
--     where
--       go _ [] = error "Pattern matching failure"
--       go a (Branch (PartialBij _ f _) h : bs) =
--         case f a of
--           Nothing -> go a bs
--           Just b -> h (Identity b)

--   funpair (Identity (a, b)) f = f (coerce a) (coerce b)
--   fununit _ x = x

--   fbchoice x _ = x

--   fabort = error "Aborted pretty-printing interpretation."

--   fcharAs (Identity c) cs
--     | c `RS.member` cs = PD (text [c])
--     | otherwise = error "charAs: Condition violated."

--   ftext s = PD (text s)
--   fempty = PD empty

--   fcat (PD d1) (PD d2) = PD (d1 <> d2)
--   fline = PD line
--   flinebreak = PD linebreak

--   fline' = PD line
--   fnespaces' = PD (text " ")

--   falign (PD d) = PD (align d)

--   fnest n (PD d) = PD (nest n d)

--   fgroup (PD d) = PD (group d)

--   fspace = PD (text " ")
--   fspaces = PD empty

-- instance Defs.Defs (Ppr d) where
--   data D (Ppr d) as a = PprRules (HList (Ppr d) as) (Ppr d a)

--   liftD = PprRules HNil
--   unliftD (PprRules HNil a) = a

--   consD x (PprRules xs r) = PprRules (HCons x xs) r

--   --   unpairRules (PprRules (VCons x y)) k = k (PprRules x) (PprRules y)

--   letrD h =
--     let PprRules (HCons a as) r = h a
--     in  PprRules as r

-- -- letrDS h =
-- --   let (a,b) = k $ pprRules $ h a
-- --   in PprRules b
-- --   where
-- --     -- Explicit decomposer to suppress an incomplete-uni-patterns warning, for this actually complete pattern.
-- --     k :: Defs.DTypeVal (Ppr d) (a <* b) -> (Ppr d a, Defs.DTypeVal (Ppr d) b)
-- --     k (Defs.VCons x y) = (x, y)

-- -- instance DocLike d => FliPprD Identity Identity (Ppr d) where
-- --   fshare = Identity
-- --   flocal = runIdentity

-- -- ffix defs = cps $ \k ->
-- --   let x = fmap2 (\k -> runRec k x) defs
-- --   in k x

pprModeMono :: (DocLike d) => Exp s (PrettyPrintingMode d) (a ~> D) -> a -> d
pprModeMono (pprInterp -> PF h) a =
  case h a of
    PD d -> d

pprMode :: (DocLike d) => FliPpr s (a ~> D) -> a -> d
pprMode (FliPpr e) = pprModeMono e
