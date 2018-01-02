{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE DataKinds #-}

module Text.FliPpr (
  -- * Types
  A, E, FliPprE(), FliPprD(), FliPpr, 
  Branch(..), type (<->)(..), In, 
  
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

  -- -- ** Fixpoints
  -- fix1, fix2, fixn, 

  -- ** knot-tying
  share, local, 

  -- ** Pretty-Printing Combinators
  spaces, space, (<#>), 

  -- ** Derived Combinators
  (<>), (<+>), (<+>.), (</>.), shares, shareN, 

  -- * Evaluator
  pprMode, parsingMode 
  ) where

import Text.FliPpr.Internal.Type
import Text.FliPpr.Internal.PrettyPrinting 
import Text.FliPpr.Internal.ParserGeneration 

import Text.FliPpr.Doc as D
import qualified Data.IntMap as IM 
import qualified Data.Map as M

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
  @shares (k1,k2) f@ is equivalent to
  @@ 
  do  fk1 <- share (f k1)
      ...
      fk2 <- share (f k2)
      return $ \k -> lookup k [(k1,fk1),...,(k2,fk2)]
  @@
-}
shares :: (Eq k, Ord k, Enum k, FliPprD m arg exp) => (k,k) -> (k -> E exp t) -> m (k -> E exp t)
shares (k1,k2) f = do
  let (m1, m2) = if k1 < k2 then (k1, k2) else (k2, k1)
  let ks = [m1..m2]
  rs <- mapM (share . f) ks
  let table = M.fromAscList $ zip ks rs 
  return $ \k -> case M.lookup k table of
                   Just m  -> m
                   Nothing -> error "shares: out of bounds" 

{- |
@sharesN n f@ is equivalent to @shares [0..n] f@, but this version is optimized a bit. 
-}
shareN :: FliPprD m arg exp => Int -> (Int -> E exp t) -> m (Int -> E exp t)
shareN n f = do 
  rs <- mapM (share . f) [0..n]
  let table = IM.fromAscList $ zip [0..n] rs
  return $ \k -> case IM.lookup k table of
                   Just m  -> m
                   Nothing -> error "shareN: out of bounds"
