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
import Text.FliPpr.Doc

newtype I a = I { unI :: a }

data Ppr d (t :: FType) where
  PD :: d -> Ppr d D
  PF :: (a -> Ppr d r) -> Ppr d (a :~> r)

instance DocLike d => FliPprC I (Ppr d) where
  fapp (PF f) (I a) = f a

  farg f = PF (f . I)

  ffix f k = let r = f r in k r

  fcase (I a) = go a
    where
      go a [] = error "Pattern matching failure"
      go a (Branch (PInv _ f g) h : bs) =
        case f a of
          Nothing -> go a bs
          Just b  -> h (I b) 


  funpair (I (a,b)) f = f (I a) (I b)

  fbchoice x _ = x

  ftext s = PD (text s)
  fempty  = PD empty

  fcat (PD d1) (PD d2) = PD (d1 <> d2)
  fline = PD line
  flinebreak = PD linebreak

  falign (PD d) = PD (align d)

  fnest n (PD d) = PD (nest n d)

  fgroup (PD d) = PD (group d)

  fspace  = PD (text " ")
  fspaces = PD empty 

pprModeMono :: (Ppr Doc (a :~> D)) -> a -> Doc
pprModeMono (PF h) a = case h a of
                      PD d -> d 
                          
pprMode :: FliPpr (a :~> D) -> a -> Doc
pprMode (FliPpr e) = pprModeE e 

