{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use camelCase" #-}

module Internal.THUtil (genTupleArgDecl) where

import Control.Monad (replicateM)
import qualified Language.Haskell.TH as TH

tupE_compat :: [TH.Exp] -> TH.Exp
#if MIN_VERSION_template_haskell(2,16,0)
tupE_compat = TH.TupE . map Just
#else
tupE_compat = TH.TupE
#endif

-- n must be no less than 2
splitTuple :: Int -> TH.Q TH.Exp
splitTuple n = do
  xs <- replicateM n (TH.newName "x")
  let (xs1, xs2) = splitAt (n `div` 2) xs
  [|
    \ $(pure $ TH.TildeP $ TH.TupP $ map TH.VarP xs) ->
      ($(pure $ tupE_compat $ map TH.VarE xs1), $(pure $ tupE_compat $ map TH.VarE xs2))
    |]

combineTuple :: Int -> TH.Q TH.Exp
combineTuple n = do
  xs <- replicateM n (TH.newName "x")
  let (xs1, xs2) = splitAt (n `div` 2) xs
  [|
    \ $(pure $ TH.TildeP $ TH.TupP $ map TH.VarP xs1) $(pure $ TH.TildeP $ TH.TupP $ map TH.VarP xs2) ->
      $(pure $ tupE_compat $ map TH.VarE xs)
    |]

genTupleLetrBody :: Int -> TH.Q TH.Exp -> TH.Q TH.Exp
genTupleLetrBody n f =
  [|
    letr $ \x -> letr $ \y -> do
      (xy', r) <- $f ($(combineTuple n) x y)
      let (x', y') = $(splitTuple n) xy'
      pure (y', (x', r))
    |]

genTupleArgDecl :: Int -> TH.Q TH.Type -> TH.Q [TH.Dec]
genTupleArgDecl n mh = do
  f <- TH.newName "f"
  xs <- replicateM n (TH.newName "t")
  h <- mh
  let h' = TH.AppT h (TH.VarT f)
  body <- [|\ff -> $(genTupleLetrBody n [|ff|])|]
  pure
    [ TH.InstanceD
        Nothing
        [TH.AppT h' (TH.VarT x) | x <- xs]
        (TH.AppT h' $ mkTupleT [TH.VarT x | x <- xs])
        [TH.ValD (TH.VarP $ TH.mkName "letr") (TH.NormalB body) []]
    ]
  where
    mkTupleT ts = foldl TH.AppT (TH.TupleT $ length ts) ts