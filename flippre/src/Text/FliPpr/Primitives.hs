{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}

module Text.FliPpr.Primitives (
  -- * Datatypes for Syntax
  FType (..),
  type D,
  type (~>),
  Exp,
  In,
  Branch (..),
  PartialBij (..),
  Phase (..),
  Phased,

  -- * Constructs

  -- ** First-Order Functions
  arg,
  app,
  (@@),
  Repr (..),

  -- ** Destructors
  case_,
  unpair,
  ununit,

  -- ** Pretty-Printing Primitives

  -- Check also for 'Text.FliPpr.Doc'.
  line',
  space,
  spaces,
  nespaces,
  nespaces',
  (<?),
  hardcat,
  (<#>),
  charAs,
  module Text.FliPpr.Doc,

  -- ** Recursive Definition Primitives
  FliPprM,
  share,
  local,
  mfixF,
  def,
  Defs.letrs,
  Defs.Defs,
  Defs.RecM (..),
  Defs.RecArg (..),

  -- ** Abort
  abort,

  -- * Ensure Closedness
  FliPpr (..),
  flippr,
) where

import qualified Data.RangeSet.List as RS

import GHC.Stack (HasCallStack, callStack)

import qualified Defs
-- for export

import qualified Text.FliPpr.Doc
import Text.FliPpr.Internal.Core

-- | Indicating that there can be zero-or-more spaces in parsing.
--   In pretty-printing, it is equivalent to @text ""@.
{-# INLINEABLE spaces #-}
spaces :: Exp s v D
spaces = Op0 Spaces

-- | In pretty-printing, it works as @text " "@. In parsing
--   it behaves a single space.
{-# INLINEABLE space #-}
space :: Exp s v D
space = Op0 Space

-- | For internal use. Use '<+>'.
{-# INLINEABLE nespaces #-}
nespaces :: Exp s v D
nespaces = space <#> spaces

-- | For internal use. Use '<+>.'.
{-# INLINEABLE nespaces' #-}
nespaces' :: Exp s v D
nespaces' = Op0 NESpaces' -- (coerce :: exp D -> E exp D) fnespaces'

-- | Unlike '(<>)' that allows spaces between concatenated elementes in parsing,
--   'hardcat' does not allow such extra spaces in parsing.
{-# INLINEABLE hardcat #-}
hardcat :: Exp s v D -> Exp s v D -> Exp s v D
hardcat = Op2 Cat

-- | A better syntax for `hardcat`.
{-# INLINE (<#>) #-}
(<#>) :: Exp s v D -> Exp s v D -> Exp s v D
(<#>) = hardcat

infixr 5 <#>

-- | Similar to 'line', but it also accepts the empty string in parsing.
{-# INLINEABLE line' #-}
line' :: Exp s v D
line' = Op0 Line'

{-# INLINEABLE abort #-}

-- | In pretty-printing 'abort' throws an error. In parsing, it accepts no strings.
abort :: (HasCallStack) => Exp s v D
abort = Op0 (Abort callStack)

-- | @arg@ represents a function in FliPpr.
-- @f@ of @arg f@ must be a linear function: @f@ must use its input exactly once.
{-# INLINEABLE arg #-}
arg :: (In v a -> Exp s v t) -> Exp s v (a ~> t)
arg = Lam

-- | Application in FliPpr. Observed that the application is restricted to @A arg a@-typed values.
{-# INLINEABLE app #-}
app :: Exp s v (a ~> t) -> In v a -> Exp s v t
app = App

-- | A synonym for 'app'. A FliPpr version of '$'.
{-# INLINE (@@) #-}
(@@) :: Exp s v (a ~> t) -> In v a -> Exp s v t
(@@) = app

infixr 0 @@

-- | Prints a 'Char' ensuring the char is in the given set.
charAs :: In v Char -> RS.RSet Char -> Exp s v D
charAs = CharAs
{-# INLINEABLE charAs #-}

-- | case branching.
{-# INLINEABLE case_ #-}
case_ :: (HasCallStack) => In v a -> [Branch (In v) (Exp s v) a r] -> Exp s v r
case_ = Case callStack

-- | A CPS style conversion from @A arg (a,b)@ to a pair of @A arg a@ and @A arg b@.
--   A typical use of 'unpair' is to implement (invertible) pattern matching in FliPpr.
--   To guarantee invertibility, @k@ of @unpair x k@ must be a linear function.
--
--   'Language.FliPpr.TH' provides 'un' and 'branch'. By using these functions,
--   one can avoid using a bit awkward 'unpair' explicitly.
{-# INLINEABLE unpair #-}
unpair :: (HasCallStack) => In v (a, b) -> (In v a -> In v b -> Exp s v r) -> Exp s v r
unpair = UnPair callStack

-- | An explicit disposal of `v ()`, required for the invertibility guarantee.
{-# INLINEABLE ununit #-}
ununit :: In v () -> Exp s v r -> Exp s v r
ununit = UnUnit

-- | Biased choice. @a <? b = a@ in parsing, but it accepts strings indicated by both @a@ and @b$ in parsing.
(<?) :: Exp s v D -> Exp s v D -> Exp s v D
(<?) = Op2 BChoice

infixr 4 <?

---------------------------------------
-- Recursive Definitions in FliPpr
---------------------------------------

-- | A restricted version of 'mfix'. Use 'Text.FliPpr.MFix' to export this
-- function as 'mfix', which is supposed to be used with
-- @RecursiveDo@/@RebindableSyntax@. For GHC over version 9.0.1, using
-- 'Text.FliPpr.QDo' with @QualifiedDo@ would be more handy.
mfixF :: (Phased s, Defs.RecArg (Exp s v) a) => (a -> FliPprM s v a) -> FliPprM s v a
mfixF = Defs.mfixDefM

-- | Useful combinator that can be used with 'letr'.
--
-- > letr $ \a -> letr $ \b ->
-- >         def body_a >>>
-- >         def body_b $
-- >         code_using_a_and_b
--
-- However, in most situations, using @RecursiveDo@ is much convenient.
--
-- > do rec a <- share body_a
-- >    rec b <- share body_b
-- >    code_using_a_and_b
-- >   where
-- >     mfix = mfixF
def :: (Functor m) => a -> m b -> m (a, b)
def a b = (a,) <$> b

-- | Sharing a computation. Roughly speaking, a (generalized) "let" in FliPpr.
--
-- For example, the following code is inefficient in parsing as it copies the
-- productions corresponding to @e@.
--
-- > ... e ... e ...
--
-- In contrast, the following version shares the productions involved in @e@.
--
-- > do v <- share e ... v ... v ...
share :: (Phased s, Defs.RecArg (Exp s v) r) => r -> FliPprM s v r
share e = Defs.letr $ \x -> return (e, x)

-- | Localize declarations.
--
-- There is a performance caveat: 'local' delimites sharing introduced by
-- 'share'. Hence, like @e@ of
--
-- > (let x = e in x) + (let x = e in x)
--
-- which evalutes twice, the following fragment
--
-- > local (do {x <- share e; pure x}) <> local (do {x <- share e; pure x})
--
-- involves the productions involved in @e@ twice.
local :: (Repr s v rep, Phased s) => FliPprM s v rep -> rep
local = toFunction . Defs.local . fmap fromFunction . runFliPprM
