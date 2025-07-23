{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternSynonyms #-}
{-# HLINT ignore "Use camelCase" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

-- | Functions to absorb the changes in Template Haskell API.
module Text.FliPpr.Internal.THCompat (
  pattern ConP_compat,
  tupE_compat,
  unboxedTupE_compat,
  viewFuncType,
) where

import qualified Language.Haskell.TH as TH

pattern ConP_compat :: TH.Name -> [TH.Pat] -> TH.Pat
#if MIN_VERSION_template_haskell(2,18,0)
pattern ConP_compat n ps <- TH.ConP n _ ps
  where
    ConP_compat n ps = TH.ConP n [] ps
#else
pattern ConP_compat n ps = TH.ConP n ps
#endif

tupE_compat :: [TH.Exp] -> TH.Exp
unboxedTupE_compat :: [TH.Exp] -> TH.Exp
#if MIN_VERSION_template_haskell(2,16,0)
tupE_compat = TH.TupE . map Just
unboxedTupE_compat = TH.UnboxedTupE . map Just
#else
tupE_compat = TH.TupE
unboxedTupE_compat = TH.UnboxedTupE
#endif

viewFuncType :: TH.Type -> Maybe (TH.Type, TH.Type)
viewFuncType (TH.AppT (TH.AppT TH.ArrowT t1) t2) = Just (t1, t2)
#if MIN_VERSION_template_haskell(2,17,0)
-- linear arrow 
viewFuncType (TH.AppT (TH.AppT (TH.AppT TH.MulArrowT _) t1) t2) = Just (t1, t2) 
#endif 
viewFuncType _ = Nothing
