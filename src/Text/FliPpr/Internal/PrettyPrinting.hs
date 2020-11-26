{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Text.FliPpr.Internal.PrettyPrinting where

import Data.Coerce
import Data.Functor.Identity
import Text.FliPpr.Doc
import Text.FliPpr.Internal.Type

data Ppr d (t :: FType) where
  PD :: d -> Ppr d D
  PF :: (a -> Ppr d r) -> Ppr d (a :~> r)

instance DocLike d => FliPprE Identity (Ppr d) where
  fapp (PF f) a = f (coerce a)

  farg f = PF (coerce f)

  fcase a = go (coerce a)
    where
      go _ [] = error "Pattern matching failure"
      go a (Branch (PartialBij _ f _) h : bs) =
        case f a of
          Nothing -> go a bs
          Just b -> h (Identity b)

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

instance DocLike d => Defs (Ppr d) where
  data Rules (Ppr d) _a where
    VT :: Ppr d a -> Rules (Ppr d) (T a)
    VP :: Rules (Ppr d) a -> Rules (Ppr d) b -> Rules (Ppr d) (a :*: b)

  lift = VT
  unlift (VT x) = x

  pairRules = VP
  unpairRules (VP x y) k = k x y

  letr h =
    let ~(VP ~(VT a) b) = h a
     in b

-- instance DocLike d => FliPprD Identity Identity (Ppr d) where
--   fshare = Identity
--   flocal = runIdentity

-- ffix defs = cps $ \k ->
--   let x = fmap2 (\k -> runRec k x) defs
--   in k x

pprModeMono :: Ppr Doc (a :~> D) -> a -> Doc
pprModeMono (PF h) a =
  case h a of
    PD d -> d

pprMode :: FliPpr (a :~> D) -> a -> Doc
pprMode (FliPpr e) = pprModeMono e
