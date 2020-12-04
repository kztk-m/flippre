{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module Text.FliPpr
  ( -- * Types
    A,
    E,
    FliPprE,
    FliPprD,
    FliPpr,
    FliPprM,
    Branch (..),
    PartialBij (..),
    In,
    Err (..),

    -- * Syntax

    -- ** Types
    FType (..),
    type D,
    type (~>),

    -- ** To wrap-up
    flippr,

    -- ** Lambda
    app,
    arg,
    (@@),

    -- ** Biased choice
    (<?),

    -- ** Case
    case_,
    unpair,
    ununit,

    -- ** knot-tying
    share,
    local,
    mfixF,
    letr, letrs,
    def,

    -- ** Pretty-Printing Combinators and Datatypes
    spaces,
    space,
    (<#>),
    line',
    module Text.FliPpr.Doc,

    -- ** Derived Combinators
    (<+>.),
    (</>.),

    -- ** Easy Definition
    define,
    Repr (..),
    --    defineR,
    defines,

    -- * Finite natural numbers
    FinNE,
    F.Fin (..),
    F.SNat (..),
    F.SNatI (..),
    F.Nat0,
    F.Nat1,
    F.Nat2,
    F.Nat3,
    F.Nat4,
    F.Nat5,
    F.Nat6,
    F.Nat7,
    F.Nat8,
    F.Nat9,
    reifySNat,
    Wit (..),

    -- ** Template Haskell
    un,
    branch,
    mkUn,

    -- ** Predefined Deconstructors
    unTrue,
    unFalse,
    unNil,
    unCons,
    unLeft,
    unRight,
    unTuple3,

    -- * Evaluator
    pprMode,
    parsingMode,
    parsingModeWith,
    parsingModeSP,
    CommentSpec (..),
    BlockCommentSpec (..),
    G.Grammar,

    -- * Utils
    Fixity (..),
    Assoc (..),
    Prec,
    opPrinter,
    is,
  )
where

import qualified Data.Fin                              as F
import qualified Data.Map                              as M
import qualified Data.Type.Nat                         as F
import           Text.FliPpr.Doc
import           Text.FliPpr.Err
import qualified Text.FliPpr.Grammar                   as G
import           Text.FliPpr.Internal.ParserGeneration
import           Text.FliPpr.Internal.PrettyPrinting
import           Text.FliPpr.Internal.Type
import           Text.FliPpr.TH

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

defines :: (FliPprD arg exp, Repr arg exp t r, F.SNatI n) => F.SNat n -> (FinNE n -> r) -> FliPprM exp (FinNE n -> r)
defines _ f = do
  let ks = [minBound .. maxBound]
  rs <- mapM (define . f) ks
  let table = M.fromList $ zip ks rs
  return $ \k -> case M.lookup k table of
    Just m  -> m
    Nothing -> error "defines_: Cannot happen."

-- -- |
-- -- @defineR (k1,k2)@ is the same as @defines [k1..k2]@, but a bit more efficient. x
-- {-# SPECIALIZE defineR ::
--   (FliPprD arg exp, Repr arg exp t r) => (Int, Int) -> (Int -> r) -> DefM (E exp) (Int -> r)
--   #-}
-- defineR :: (Eq k, Ord k, Enum k, FliPprD arg exp, Repr arg exp t r) => (k, k) -> (k -> r) -> DefM (E exp) (k -> r)
-- defineR (k1, k2) f = do
--   let (m1, m2) = if k1 < k2 then (k1, k2) else (k2, k1)
--   let ks = [m1 .. m2]
--   rs <- mapM (define . f) ks
--   let table = M.fromAscList $ zip ks rs
--   return $ \k -> case M.lookup k table of
--     Just m -> m
--     Nothing -> error "defineR: out of bounds"

-- -- |
-- -- @defines [k1,...,kn] f@ is equivalent to:
-- --
-- -- @
-- --   do  fk1 <- define (f k1)
-- --       ...
-- --       fk2 <- define (f k2)
-- --       return $ \k -> lookup k [(k1,fk1),...,(k2,fk2)]
-- -- @
-- {-# SPECIALIZE defines ::
--   (FliPprD arg exp, Repr arg exp t r) => [Int] -> (Int -> r) -> DefM (E exp) (Int -> r)
--   #-}
-- defines :: (Eq k, Ord k, FliPprD arg exp, Repr arg exp t r) => [k] -> (k -> r) -> DefM (E exp) (k -> r)
-- defines ks f = do
--   rs <- mapM (define . f) ks
--   let table = M.fromList $ zip ks rs
--   return $ \k -> case M.lookup k table of
--     Just m -> m
--     Nothing -> error "defines: out of bounds"

is :: (FliPprE arg exp, Eq c, Show c) => c -> E exp r -> Branch (A arg) (E exp) c r
is c f =
  PartialBij
    ("is " ++ show c)
    (\x -> if x == c then Just () else Nothing)
    (\_ -> Just c)
    `Branch` (\x -> ununit x f)


-- |
-- The function 'define' provides an effective way to avoid writing 'app' and 'arg'.
-- We can write
--
-- >  f <- define $ \i -> ...
-- >  ... f a ...
--
-- instead of:
--
-- >  f <- share $ arg $ \i -> ...
-- >  ... f `app` a ...
--
-- It works also with recursive defintions.
-- We can write
--
-- >  rec f <- define $ \i -> ... f a ...
--
-- instead of:
--
-- >  rec f <- share $ arg $ \i -> ... f `app` a ...
define :: (FliPprD arg exp, Repr arg exp t r) => r -> FliPprM exp r
define = share

type Prec = Int

data Fixity = Fixity Assoc Prec

data Assoc
  = AssocL
  | AssocR
  | AssocN

opPrinter ::
  (DocLike d, Ord n, Num n) =>
  Fixity ->
  (d -> d -> d) ->
  (n -> d) ->
  (n -> d) ->
  (n -> d)
opPrinter (Fixity a opPrec) opD ppr1 ppr2 k =
  let (dl, dr) = case a of
        AssocL -> (0, 1)
        AssocR -> (1, 0)
        AssocN -> (0, 0)
   in ifParens (k > fromIntegral opPrec) $ opD (ppr1 (fromIntegral opPrec + dl)) (ppr2 (fromIntegral opPrec + dr))
  where
    ifParens b = if b then parens else id

$(mkUn ''Bool)
$(mkUn ''(:))
$(mkUn ''Either)
$(mkUn ''(,,))
