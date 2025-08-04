{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

-- | Module supposed to be used with @RebindableSyntax@.
module Text.FliPpr.Mfix (mfix) where

import Text.FliPpr

-- | A type-restricted version of 'Control.Monad.mfix'. This function is supposed to be used with the combination of
-- @RecursiveDo@ and @RebindableSyntax@ so that the desugaring of @do { rec a <- e; ... }@ will use
-- this version.
--
-- With this, one can define "recursive" definitions more naturally as:
--
-- @
-- {# LANGUAGE RecursiveDo, RebindableSyntax #-}
--
-- someFunc = do
--    rec f <- share $ fdef
--        g <- share $ gdef
--    m
-- @
--
-- instead of
--
-- @
-- someFunc =
--   letr $ \f ->
--   letr $ \g ->
--     def fdef >>>
--     def gdef $ do
--       m
-- @
--
-- [NOTE] Since parsers need to identify recursive structures, recursive
-- definitions of pretty-printer are problematic in FliPpr. Hence, FliPpr
-- provides a few combinators (such as 'letr' and 'letrs') for explicit
-- recursive definitions. However, using these combinators make programs
-- awkward. This module is supposed to be a remedy. We could use impure
-- operations to extract graph structures. Indeed in an earlier version, we used
-- 'STRef' to detect recursive structures. However, this design turned out to be
-- sources of unclear non-termination bugs.
mfix :: (Arg (FliPprM s v) a) => (a -> FliPprM s v a) -> FliPprM s v a
mfix = mfixF
