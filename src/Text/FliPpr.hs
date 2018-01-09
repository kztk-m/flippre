{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}

module Text.FliPpr (
  -- * Types
  A, E, FliPprE, FliPprD, FliPpr, 
  Branch(..), PartialBij(..), In, Err(..), 
  
  -- * Syntax
  -- ** Types
  FType(..), 

  -- ** To wrap-up
  flippr, 
 
  -- ** Lambda 
  app, arg, (@@),

  -- ** Biased choice
  (<?),

  -- ** Case
  case_, unpair,

  -- ** knot-tying
  share, local, 

  -- ** Pretty-Printing Combinators and Datatypes
  spaces, space, (<#>), 
  module Text.FliPpr.Doc, 

  -- ** Derived Combinators
  (<+>.), (</>.), 

  -- ** Easy Definition
  define, Repr(..), defineR, defines,

  -- ** Template Haskell
  un, branch, mkUn, 

  -- ** Predefined Deconstructors 
  unTrue, unFalse, unNil, unCons,
  unLeft, unRight, unTuple3, 
  
  -- * Evaluator
  pprMode, parsingMode, parsingModeWith, parsingModeSP,
  CommentSpec(..), BlockCommentSpec(..),
  G.Grammar, G.OpenGrammar,

  -- * Utils
  Fixity(..), Assoc(..), Prec, opPrinter, 
  ) where

import Text.FliPpr.Internal.Type
import Text.FliPpr.Internal.PrettyPrinting 
import Text.FliPpr.Internal.ParserGeneration 
import Text.FliPpr.TH

import Text.FliPpr.Doc 
import Text.FliPpr.Err

import qualified Data.Map as M

import qualified Text.FliPpr.Internal.GrammarST as G

-- | In pretty-printing, '<+>.' behaves as '<+>', but in parser construction,
--   it behaves as '<>'.
(<+>.) :: FliPprE arg exp => E exp D -> E exp D -> E exp D
x <+>. y = x <#> nespaces' <#> y

-- | In pretty-printing, '</>.' behaves as '</>', but in parser construction,
--   it behaves as '<>'.
(</>.) :: FliPprE arg exp => E exp D -> E exp D -> E exp D
x </>. y = x <#> line' <#> y

infixr 4 <+>.
infixr 4 </>.

{- |
@defineR (k1,k2)@ is the same as @defines [k1..k2]@, but a bit more efficient. x
-}

{-# SPECIALIZE
      defineR :: (FliPprD m arg exp, Repr arg exp t r) => (Int,Int) -> (Int -> r) -> m (Int -> r)
  #-}
  
defineR :: (Eq k, Ord k, Enum k, FliPprD m arg exp, Repr arg exp t r) => (k,k) -> (k -> r) -> m (k -> r)
defineR (k1,k2) f = do
  let (m1, m2) = if k1 < k2 then (k1, k2) else (k2, k1)
  let ks = [m1..m2]
  rs <- mapM (define . f) ks
  let table = M.fromAscList $ zip ks rs 
  return $ \k -> case M.lookup k table of
                   Just m  -> m
                   Nothing -> error "defineR: out of bounds" 

{- |
@defines [k1,...,kn] f@ is equivalent to:

@ 
  do  fk1 <- define (f k1)
      ...
      fk2 <- define (f k2)
      return $ \k -> lookup k [(k1,fk1),...,(k2,fk2)]
@
-}

{-# SPECIALIZE
      defines :: (FliPprD m arg exp, Repr arg exp t r) => [Int] -> (Int -> r) -> m (Int -> r)
  #-}
defines :: (Eq k, Ord k, FliPprD m arg exp, Repr arg exp t r) => [k] -> (k -> r) -> m (k -> r)
defines ks f = do 
  rs <- mapM (define . f) ks
  let table = M.fromList $ zip ks rs
  return $ \k -> case M.lookup k table of
                   Just m  -> m
                   Nothing -> error "defines: out of bounds"

{- |
The type class 'Repr' provides the two method 'toFunction' and 'fromFunction'.
-}

class Repr (arg :: * -> *) exp (t :: FType) r | exp -> arg, exp t -> r, r -> arg exp t where
  toFunction   :: E exp t -> r
  -- ^ @toFunction :: E exp (a1 :~> ... :~> an :~> D) -> A arg a1 -> ... -> A arg an -> E exp D@
  
  fromFunction :: r -> E exp t 
  -- ^ @fromFunction :: A arg a1 -> ... -> A arg an -> E exp D -> E exp (a1 :~> ... :~> an :~> D)@

instance FliPprE arg exp => Repr arg exp D (E exp D) where
  toFunction = id
  fromFunction = id 

instance (FliPprE arg exp, Repr arg exp t r, In a) => Repr arg exp (a :~> t) (A arg a -> r) where
  toFunction f = \a -> toFunction (f `app` a) 
  fromFunction k = arg (fromFunction . k)

{- |
The function 'define' provides an effective way to avoid writing 'app' and 'arg'.
We can write

>  f <- define $ \i -> ...
>  ... f a ...

instead of:

>  f <- share $ arg $ \i -> ...
>  ... f `app` a ...

It works also with recursive defintions.
We can write

>  rec f <- define $ \i -> ... f a ...  

instead of:

>  rec f <- share $ arg $ \i -> ... f `app` a ... 

-}
define :: (FliPprD m arg exp, Repr arg exp t r) => r -> m r
define f = do
  f' <- share $ fromFunction f
  return $ toFunction f' 

type Prec = Int 

data Fixity = Fixity Assoc Prec

data Assoc = AssocL
           | AssocR
           | AssocN


opPrinter :: DocLike d => 
             Fixity -> (d -> d -> d) -> (Prec -> d) -> (Prec -> d) -> (Prec -> d)
opPrinter (Fixity a opPrec) opD ppr1 ppr2 k =
  let (dl, dr) = case a of
                   AssocL -> (0, 1)
                   AssocR -> (1, 0)
                   AssocN -> (0, 0)                              
  in ifParens (k > opPrec) $ opD (ppr1 (opPrec+dl)) (ppr2 (opPrec+dr))
  where
    ifParens b = if b then parens else id 

$(mkUn ''Bool)
$(mkUn ''(:))
$(mkUn ''Either)
$(mkUn ''(,,))

  
  
