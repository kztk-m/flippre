{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

{-# LANGUAGE MultiParamTypeClasses #-}
module Text.FliPpr.Internal.PrettyPrinting where

import Text.FliPpr.Internal.Type
import Data.Functor.Identity 
import Control.Monad.Fix (MonadFix(..))
import Text.FliPpr.Doc

newtype I a = I { unI :: a }

data Ppr d (t :: FType) where
  PD :: d -> Ppr d D
  PF :: (a -> Ppr d r) -> Ppr d (a :~> r)

instance Renderable d => Renderable (Ppr d D) where
  render w (PD d) = render w d 

instance DocLike d => FliPprE I (Ppr d) where
  app (PF f) (I a) = f a

  arg f = PF (f . I)

  ffix f = let r = f r in r

  case_ (I a) = go a
    where
      go a [] = error "Pattern matching failure"
      go a (Branch (PInv f g) h : bs) =
        case f a of
          Nothing -> go a bs
          Just b  -> h (I b) 


  unpair (I (a,b)) f = f (I a) (I b)

  x <? _ = x

  ftext s = PD (text s)
  fempty  = PD empty

  fcat (PD d1) (PD d2) = PD (d1 <> d2)
  fline = PD line
  flinebreak = PD linebreak

  falign (PD d) = PD (align d)

  fnest n (PD d) = PD (nest n d)

  fgroup (PD d) = PD (group d)

  fspaces = PD empty 

instance (MonadFix m, DocLike d) => FliPpr I (Ppr d) m where
  rule = pure 
  

toPprMono :: MonadFix m => DocLike d => m (Ppr d (a :~> D)) -> a -> m d
toPprMono m x = do
  PF h <- m 
  case h x of
    PD d -> return d

toPpr :: (DocLike d, MonadFix m) => (forall arg exp r. FliPpr arg exp r => r (exp (a :~> D))) -> a -> m d
toPpr = toPprMono

