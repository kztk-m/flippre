{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Text.FliPpr.Internal.PrettyPrinting (
  pprMode,
  pprModeMono,
  Ppr (..),
) where

import Data.Coerce
import Data.Functor.Identity
import Text.FliPpr.Doc
import Text.FliPpr.Internal.Type

import qualified Data.RangeSet.List as RS
import qualified Defs

import Text.FliPpr.Internal.HList

data Ppr d (t :: FType) where
  PD :: !d -> Ppr d D
  PF :: !(a -> Ppr d r) -> Ppr d (a ~> r)

instance (DocLike d) => FliPprE Identity (Ppr d) where
  fapp (PF f) a = f (coerce a)

  farg f = PF (coerce f)

  fcase e0 = go (coerce e0)
    where
      go _ [] = error "Pattern matching failure"
      go a (Branch (PartialBij _ f _) h : bs) =
        case f a of
          Nothing -> go a bs
          Just b -> h (Identity b)

  funpair (Identity (a, b)) f = f (coerce a) (coerce b)
  fununit _ x = x

  fbchoice x _ = x

  fabort = error "Aborted pretty-printing interpretation."

  fcharAs (Identity c) cs
    | c `RS.member` cs = PD (text [c])
    | otherwise = error "charAs: Condition violated."

  ftext s = PD (text s)
  fempty = PD empty

  fcat (PD d1) (PD d2) = PD (d1 <> d2)
  fline = PD line
  flinebreak = PD linebreak

  fline' = PD line
  fnespaces' = PD (text " ")

  falign (PD d) = PD (align d)

  fnest n (PD d) = PD (nest n d)

  fgroup (PD d) = PD (group d)

  fspace = PD (text " ")
  fspaces = PD empty

instance Defs.Defs (Ppr d) where
  data D (Ppr d) as a = PprRules (HList (Ppr d) as) (Ppr d a)

  liftD = PprRules HNil
  unliftD (PprRules HNil a) = a

  consD x (PprRules xs r) = PprRules (HCons x xs) r

  --   unpairRules (PprRules (VCons x y)) k = k (PprRules x) (PprRules y)

  letrD h =
    let PprRules (HCons a as) r = h a
    in  PprRules as r

-- letrDS h =
--   let (a,b) = k $ pprRules $ h a
--   in PprRules b
--   where
--     -- Explicit decomposer to suppress an incomplete-uni-patterns warning, for this actually complete pattern.
--     k :: Defs.DTypeVal (Ppr d) (a <* b) -> (Ppr d a, Defs.DTypeVal (Ppr d) b)
--     k (Defs.VCons x y) = (x, y)

-- instance DocLike d => FliPprD Identity Identity (Ppr d) where
--   fshare = Identity
--   flocal = runIdentity

-- ffix defs = cps $ \k ->
--   let x = fmap2 (\k -> runRec k x) defs
--   in k x

pprModeMono :: Ppr d (a ~> D) -> a -> d
pprModeMono (PF h) a =
  case h a of
    PD d -> d

pprMode :: (DocLike d) => FliPpr (a ~> D) -> a -> d
pprMode (FliPpr e) = pprModeMono e
