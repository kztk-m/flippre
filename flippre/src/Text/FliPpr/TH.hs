{-# LANGUAGE CPP              #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms  #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TupleSections    #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module Text.FliPpr.TH
  (
    un, mkUn, branch, pat,
  ) where

import           Control.Arrow                (second)
import           Data.Char                    as C
import           Language.Haskell.TH          as TH
import           Language.Haskell.TH.Datatype as TH
import           Prelude                      hiding (exp)
import           Text.FliPpr.Internal.Type
import           Text.FliPpr.Pat              as Pat


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


-- | Generate "un" functions for datatypes. This does not work well for
-- non-letter constructor names in general, except for @[]@, @(:)@, and tuples.

mkUn :: TH.Name -> Q [TH.Dec]
mkUn n = do
  info <- TH.reifyDatatype n
  dss <- mapM makeUn (TH.datatypeCons info)
  return $ concat dss
  where
    makeUn :: TH.ConstructorInfo -> Q [TH.Dec]
    makeUn cinfo = do
      let cn = TH.constructorName cinfo
      let bn = TH.nameBase cn
      fn <- makeUnName bn
      (t, e) <- unGen cn
      -- let sigd = TH.SigD fn t
      -- (sigd:) <$> [d| $(TH.varP fn) = $(return e) |]
      return [TH.SigD fn t, TH.ValD (TH.VarP fn) (TH.NormalB e) []]
      where
        makeUnName :: String -> Q TH.Name
        makeUnName ":" = return $ TH.mkName "unCons"
        makeUnName "[]" = return $ TH.mkName "unNil"
        makeUnName s | C.isUpper (head s) = return $ TH.mkName $ "un" ++ s
        makeUnName s =
          case [i | i <- 0 : [2 .. 5], s == TH.nameBase (TH.tupleDataName i)] of
            j : _ -> return $ TH.mkName $ "unTuple" ++ show j
            _ -> fail $ "mkUn does not support non-letter constructors in general: " ++ show n

{- |
Make an (injective) deconstructor from a constructor.

For example, we have:

>>> :t $(un '(:))
$(un '(:))
  :: forall (arg :: * -> *) (exp :: FType -> *) a (r :: FType).
     (FliPprE arg exp, Eq a) =>
     (A arg a -> A arg [a] -> E exp r) -> Branch (A arg) (E exp) [a] r

>>> :t $(un 'Left)
$(un 'Left)
  :: forall (arg :: * -> *) (exp :: FType -> *) a (r :: FType) b.
     (FliPprE arg exp, Eq a) =>
     (A arg a -> E exp r) -> Branch (A arg) (E exp) (Either a b) r
-}
un :: TH.Name -> Q TH.Exp
un n = do
  (t, e) <- unGen n
  [|$(return e) :: $(return t)|]

unGen :: TH.Name -> Q (TH.Type, TH.Exp)
unGen cname = do
  -- We do not use 'reifyConstructor' from th-abstraction, as we want to check whether
  -- the constructor is the only one constructor of the datatype or not.
  cinfo <- TH.reify cname
  case cinfo of
    TH.DataConI _ ty tyname -> do
      let n = numberOfArgs ty
      isSing <- isSingleton tyname
      let f = makeForward cname n isSing
      let fi = makeBackward cname n
      let exp = makeBody n
      t <- makeTy ty
      r <-
        [|
          \e ->
            PartialBij $(TH.litE $ TH.stringL $ TH.nameBase cname) $f $fi
              `Branch` $(exp) e
          |]
      return (t, r)
    _ ->
      fail $ "un: " ++ show cname ++ " is not a constructor"
  where
    -- ... => a -> b -> c  ---> ... (A arg a -> A arg b -> E arg t) -> Branch (A arg) (E exp) c t
    makeTy :: TH.Type -> Q TH.Type
    makeTy ty = do
      let (_ctxt, body) = splitType ty
      (argsTy, retTy) <- parseType body
      arg_ <- TH.varT =<< TH.newName "arg"
      exp_ <- TH.varT =<< TH.newName "exp"
      res_ <- TH.varT =<< TH.newName "r"
      let ar = return arg_
      let exp = return exp_
      let res = return res_
      let contTy = foldr (\a r -> [t|A $ar $(return a) -> $r|]) [t|E $exp $res|] argsTy
      let resultTy = [t|Branch (A $ar) (E $exp) $(return retTy) $res|]
      -- let inCtxt t = do
      --       cs <- mapM (\a -> [t|In $(return a)|]) argsTy
      --       TH.ForallT [] cs <$> t
      -- [t|FliPprE $ar $exp => $(inCtxt [t|$contTy -> $resultTy|])|]
      [t| FliPprE $ar $exp => $contTy -> $resultTy |]
      where
        splitType :: TH.Type -> (TH.Type -> TH.Type, TH.Type)
        splitType (TH.ForallT tvs ctxt t) =
          let (k, t') = splitType t
           in (TH.ForallT tvs ctxt . k, t')
        splitType t = (id, t)

    -- FIXME: Generate Error Messages
    parseType :: TH.Type -> Q ([TH.Type], TH.Type)
    parseType (TH.AppT (TH.AppT ArrowT t1) t2) = do
      (args, ret) <- parseType t2
      return (t1 : args, ret)
    parseType (TH.SigT _ _) = fail "Kind signatures are not supported yet."

#if MIN_VERSION_template_haskell(2,17,0)
    parseType (TH.AppT (TH.AppT (TH.AppT TH.MulArrowT _) t1) t2) = do
      (args, ret) <- parseType t2
      return (t1 : args, ret)
#endif

    parseType t = return ([], t)

    -- numberOfArgs :: TH.Type -> Int
    -- numberOfArgs (TH.AppT (TH.AppT ArrowT _) t2) = numberOfArgs t2 + 1
    -- numberOfArgs (TH.ForallT _ _ t) = numberOfArgs t
    -- numberOfArgs (TH.SigT t _) = numberOfArgs t
    -- numberOfArgs (TH.ParensT t) = numberOfArgs t
    -- numberOfArgs _ = 0

    -- makeForward :: TH.Name -> Int -> Bool -> Q TH.Exp
    -- makeForward cn n isSing = do
    --   vs <- mapM (\i -> TH.newName ("x" ++ show i)) [1 .. n]
    --   let pat = return $ TH.ConP cn $ map TH.VarP vs
    --   let exp = return $ foldr (\x r -> TH.TupE [TH.VarE x, r]) (TH.TupE []) vs
    --   if isSing
    --     then [|\ $(pat) -> Just $(exp)|]
    --     else [|\x -> case x of $(pat) -> Just $(exp); _ -> Nothing|]

    -- makeBackward :: TH.Name -> Int -> Q TH.Exp
    -- makeBackward cn n = do
    --   vs <- mapM (\i -> TH.newName ("x" ++ show i)) [1 .. n]
    --   let pat = return $ foldr (\x r -> TH.TupP [TH.VarP x, r]) (TH.TupP []) vs
    --   let exp = return $ foldl TH.AppE (TH.ConE cn) $ map TH.VarE vs
    --   [|\ $(pat) -> Just $(exp)|]

    makeBody :: Int -> Q TH.Exp
    makeBody n = do
      vs <- mapM (\i -> TH.newName ("x" ++ show i)) [1 .. n]
      x <- TH.newName "_u"
      z <- TH.newName "z"
      [|\ $(TH.varP z) $(TH.varP x) -> $(go vs vs x z)|]
      where
        go [] ovs x z =
          [|ununit $(TH.varE x) $(return $ foldl TH.AppE (TH.VarE z) $ map TH.VarE ovs)|]
        go (v : vs) ovs x z = do
          x' <- TH.newName "_u"
          [|
            unpair $(TH.varE x) $
              \ $(TH.varP v) $(TH.varP x') -> $(go vs ovs x' z)
            |]

-- |
-- A syntactic sugar for 'Branch'.
-- A typical usage is:
--
-- > $(branch [p| a : x |] [| ppr `app` a <> pprs `app` x |])
--
-- The variables in the pattern must be different from any other bound variable in the scope.
-- Otherwise, the same variable in the body refers to the bound variable,
-- instead of the one introduced in the pattern.
branch :: Q TH.Pat -> Q TH.Exp -> Q TH.Exp
branch patQ expQ = do
  p <- patQ
  exp <- expQ
  let vs = gatherVarNames p
  let f = makeForward' p vs
  let fi = makeBackward' p vs
  let nf = "<" ++ pprint p ++ ">"
  [|
    Branch
      (PartialBij $(TH.litE $ TH.stringL nf) $f $fi)
      $(makeBody exp vs)
    |]
  where
    gatherVarNames :: TH.Pat -> [TH.Name]
    gatherVarNames = flip go []
      where
        go (TH.LitP _) r = r
        go (TH.VarP n) r = n : r
        go (TH.TupP ps) r = foldr go r ps
        go (TH.UnboxedTupP ps) r = foldr go r ps
        go (ConP_compat _ ps) r = foldr go r ps
        go (TH.InfixP p1 _ p2) r = go p1 (go p2 r)
        go (TH.UInfixP p1 _ p2) r = go p1 (go p2 r)
        go (TH.ParensP p) r = go p r
        go (TH.TildeP p) r = go p r
        go (TH.BangP p) r = go p r
        go TH.WildP r = r
        go (TH.RecP _ fs) r = foldr (go . snd) r fs
        go (TH.ListP ps) r = foldr go r ps
        go (TH.SigP p _) r = go p r
        go p _ = error $ "branch: Not supported: " ++ pprint p

    patToExp :: TH.Pat -> TH.Exp
    patToExp (TH.LitP l) = TH.LitE l
    patToExp (TH.VarP x) = TH.VarE x
    patToExp (TH.TupP ps) = tupE_compat (map patToExp ps)
    patToExp (TH.UnboxedTupP ps) = unboxedTupE_compat (map patToExp ps)
    patToExp (ConP_compat c ps) = foldl TH.AppE (TH.ConE c) $ map patToExp ps
    patToExp (TH.InfixP p1 n p2) = TH.InfixE (Just $ patToExp p1) (TH.ConE n) (Just $ patToExp p2)
    patToExp (TH.UInfixP p1 n p2) = TH.UInfixE (patToExp p1) (TH.ConE n) (patToExp p2)
    patToExp (TH.ParensP p) = TH.ParensE (patToExp p)
    patToExp (TH.TildeP p) = patToExp p
    patToExp (TH.BangP p) = patToExp p
    patToExp TH.WildP = tupE_compat []
    patToExp (TH.RecP n fs) = TH.RecConE n $ map (second patToExp) fs
    patToExp (TH.ListP ps) = TH.ListE (map patToExp ps)
    patToExp (TH.SigP p t) = TH.SigE (patToExp p) t
    patToExp p = error $ "branch: Not supported: " ++ pprint p

    makeForward' :: TH.Pat -> [TH.Name] -> Q TH.Exp
    makeForward' pat0 vs = do
      let e = return $ foldr (\a r -> tupE_compat [TH.VarE a, r]) (tupE_compat []) vs
      [|\x -> case x of $(return pat0) -> Just $(e); _ -> Nothing|]

    makeBackward' :: TH.Pat -> [TH.Name] -> Q TH.Exp
    makeBackward' pat0 vs = do
      let p = return $ foldr (\a r -> TH.TupP [TH.VarP a, r]) (TH.TupP []) vs
      [|\ $p -> Just $(return $ patToExp pat0)|]

    makeBody :: TH.Exp -> [TH.Name] -> Q TH.Exp
    makeBody exp vs = do
      x <- TH.newName "_u"
      [|\ $(TH.varP x) -> $(go vs x)|]
      where
        go [] x = [|ununit $(TH.varE x) $(return exp)|]
        go (u : us) x = do
          x' <- TH.newName "_u"
          [|
            unpair $(TH.varE x) $
              \ $(TH.varP u) $(if null vs then TH.wildP else TH.varP x') -> $(go us x')
            |]

{- |

This provide the most general way for pattern matching in this module.
The generated pattern-like expressions are supposed to be used together with 'br' in 'Text.FliPpr.Pat'.

>>> :t $(pat '(:))
$(pat '(:))
  :: forall env'1 env'2 a env.
     PatT env'1 env'2 a -> PatT env env'1 [a] -> PatT env env'2 [a]


>>> :t $(pat 'True)
$(pat 'True) :: forall env'. PatT env' env' Bool


>>> :t $(pat 'Left)
$(pat 'Left) :: forall env env' a b. PatT env env' a -> PatT env env' (Either a b)


>>> :t $(pat '(,,,))
$(pat '(,,,))
  :: forall env'1 env'2 a env'3 b env'4 c env d.
     PatT env'1 env'2 a
     -> PatT env'3 env'1 b
     -> PatT env'4 env'3 c
     -> PatT env env'4 d
     -> PatT env env'2 (a, b, c, d)

-}

pat :: TH.Name -> Q TH.Exp
pat cname = do
  cinfo <- TH.reify cname
  case cinfo of
    TH.DataConI _ ty tyname -> do
      let n = numberOfArgs ty
      isSing <- isSingleton tyname
      let f = makeForward cname n isSing
      let fi = makeBackward cname n
      let pBij = [| PartialBij $(TH.litE $ TH.stringL $ TH.nameBase cname) $f $fi |]
      mkLift n [| Pat.lift $pBij |]
    _ ->
      fail $ "pat: " ++ show cname ++ " is not a constructor or unsupported name."

    where
      -- mkLift 0 f = [| $f unit |]
      -- mkLift 1 f = [| \x -> $f (x &. unit) |]
      -- mkLift 2 f = [| \x1 x2 -> $f (x1 &. x2 &. unit) |]
      -- ...
      mkLift :: Int -> Q TH.Exp -> Q TH.Exp
      mkLift n f = do
        vs <- mapM (\i -> TH.newName ("x" ++ show i)) [1..n]
        let body = foldr (\x r -> [| $(TH.varE x) Pat.&. $r |] ) [| Pat.unit |] vs
        foldr (\x r -> [| \ $(TH.varP x) -> $r |] ) [| $f $body |] vs


numberOfArgs :: TH.Type -> Int
numberOfArgs (TH.AppT (TH.AppT ArrowT _) t2) = numberOfArgs t2 + 1
numberOfArgs (TH.ForallT _ _ t)              = numberOfArgs t
numberOfArgs (TH.SigT t _)                   = numberOfArgs t
numberOfArgs (TH.ParensT t)                  = numberOfArgs t

#if MIN_VERSION_template_haskell(2,17,0)
numberOfArgs (TH.AppT (TH.AppT (TH.AppT TH.MulArrowT _) _) t2) = numberOfArgs t2 + 1
#endif

numberOfArgs _                               = 0

makeForward :: TH.Name -> Int -> Bool -> Q TH.Exp
makeForward cn n isSing = do
  vs <- mapM (\i -> TH.newName ("x" ++ show i)) [1 .. n]
  let p = return $ ConP_compat cn $ map TH.VarP vs
  let exp = return $ foldr (\x r -> tupE_compat [TH.VarE x, r]) (tupE_compat []) vs
  if isSing
    then [|\ $p -> Just $(exp)|]
    else [|\x -> case x of $(p) -> Just $(exp); _ -> Nothing|]

makeBackward :: TH.Name -> Int -> Q TH.Exp
makeBackward cn n = do
  vs <- mapM (\i -> TH.newName ("x" ++ show i)) [1 .. n]
  let p = return $ foldr (\x r -> TH.TupP [TH.VarP x, r]) (TH.TupP []) vs
  let exp = return $ foldl TH.AppE (TH.ConE cn) $ map TH.VarE vs
  [|\ $p -> Just $(exp)|]

isSingleton :: TH.Name -> Q Bool
isSingleton tyname = do
  info <- TH.reify tyname
  case info of
    TH.TyConI dec ->
      case dec of
        TH.DataD _ _ _ _ cs _ ->
          return $ length cs <= 1
        TH.NewtypeD {} ->
          return True
        TH.DataInstD _ _ _ _ cs _ ->
          return $ length cs <= 1
        TH.NewtypeInstD {} ->
          return True
        _ ->
          return False
    _ ->
      return False
