{-# LANGUAGE ExplicitNamespaces #-}

module Text.FliPpr (
  -- * Types
  A, E, FliPprE(), FliPprD(),
  Branch(..), type (<->)(..), In, 
  
  -- * Syntax
  -- ** Lambda 
  app, arg, (@@),

  -- ** Biased choice
  (<?),

  -- ** Case
  case_, unpair,

  -- -- ** Fixpoints
  -- fix1, fix2, fixn, 

  -- ** tying
  share, 

  -- ** Raw Pretty-Printing Combinators
  hardcat, spaces, space, 


  -- * Evaluator
  pprMode, parsingMode 
  ) where

import Text.FliPpr.Internal.Type
import Text.FliPpr.Internal.PrettyPrinting 
import Text.FliPpr.Internal.ParserGeneration 


