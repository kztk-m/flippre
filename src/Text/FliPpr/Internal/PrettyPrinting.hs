{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Text.FliPpr.Internal.PrettyPrinting where

import           Data.Coerce
import           Data.Functor.Identity
import           Text.FliPpr.Doc
import           Text.FliPpr.Internal.Type

import qualified Text.FliPpr.Internal.Defs as Defs

data Ppr d (t :: FType) where
  PD :: d -> Ppr d D
  PF :: (a -> Ppr d r) -> Ppr d (a ~> r)

instance DocLike d => FliPprE Identity (Ppr d) where
  fapp (PF f) a = f (coerce a)

  farg f = PF (coerce f)

  fcase e0 = go (coerce e0)
    where
      go _ [] = error "Pattern matching failure"
      go a (Branch (PartialBij _ f _) h : bs) =
        case f a of
          Nothing -> go a bs
          Just b  -> h (Identity b)

  funpair (Identity (a, b)) f = f (coerce a) (coerce b)
  fununit _ x = x

  fbchoice x _ = x

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

instance DocLike d => Defs.Defs (Ppr d) where
  newtype Fs (Ppr d) a = PprRules {pprRules :: Defs.DTypeVal (Ppr d) a}

  liftDS = PprRules . Defs.VT
  unliftDS (PprRules (Defs.VT x)) = x

  pairDS (PprRules x) (PprRules y) = PprRules (Defs.VProd x y)

  --   unpairRules (PprRules (VProd x y)) k = k (PprRules x) (PprRules y)

  letrDS h =
    let ~(Defs.VProd ~(Defs.VT a) b) = pprRules $ h a
     in PprRules b

-- instance DocLike d => FliPprD Identity Identity (Ppr d) where
--   fshare = Identity
--   flocal = runIdentity

-- ffix defs = cps $ \k ->
--   let x = fmap2 (\k -> runRec k x) defs
--   in k x

pprModeMono :: Ppr Doc (a ~> D) -> a -> Doc
pprModeMono (PF h) a =
  case h a of
    PD d -> d

pprMode :: FliPpr (a ~> D) -> a -> Doc
pprMode (FliPpr e) = pprModeMono e
