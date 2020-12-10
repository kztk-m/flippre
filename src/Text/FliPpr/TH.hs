{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections   #-}

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

{-
Needs FlexibleContents.
-}
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
      return $ [TH.SigD fn t, TH.ValD (TH.VarP fn) (TH.NormalB e) []]
      where
        makeUnName :: String -> Q TH.Name
        makeUnName ":" = return $ TH.mkName "unCons"
        makeUnName "[]" = return $ TH.mkName "unNil"
        makeUnName s | C.isUpper (head s) = return $ TH.mkName $ "un" ++ s
        makeUnName s =
          case [i | i <- 0 : [2 .. 5], s == TH.nameBase (TH.tupleDataName i)] of
            j : _ -> return $ TH.mkName $ "unTuple" ++ show j
            _ -> fail $ "mkUn does not support non-letter constructors in general: " ++ show n

-- |
-- Make an (injective) deconstructor from a constructor.
--
-- For example, we have:
--
-- >>> :t $(un '(:))
-- \$(un '(:))
--   :: (FliPprE arg exp, Eq a, Data.Typeable.Internal.Typeable a) =>
--      (A arg a -> A arg [a] -> E exp t) -> Branch (A arg) (E exp) [a] t
--
-- >>> :t $(un 'Left)
-- \$(un 'Left)
--   :: (FliPprE arg exp, Eq a, Data.Typeable.Internal.Typeable a) =>
--      (A arg a -> E exp t1) -> Branch (A arg) (E exp) (Either a t) t1
--
-- In general, use of 'un' requires FlexibleContents.
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
      let inCtxt t = do
            cs <- mapM (\a -> [t|In $(return a)|]) argsTy
            TH.ForallT [] cs <$> t
      [t|FliPprE $ar $exp => $(inCtxt [t|$contTy -> $resultTy|])|]
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
-- @@
--  $(branch [p| a : x |] [| ppr `app` a <> pprs `app` x |])
-- @@
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
        go (TH.ConP _ ps) r = foldr go r ps
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
    patToExp (TH.TupP ps) = TH.TupE (map patToExp ps)
    patToExp (TH.UnboxedTupP ps) = TH.UnboxedTupE (map patToExp ps)
    patToExp (TH.ConP c ps) = foldl TH.AppE (TH.ConE c) $ map patToExp ps
    patToExp (TH.InfixP p1 n p2) = TH.InfixE (Just $ patToExp p1) (TH.ConE n) (Just $ patToExp p2)
    patToExp (TH.UInfixP p1 n p2) = TH.UInfixE (patToExp p1) (TH.ConE n) (patToExp p2)
    patToExp (TH.ParensP p) = TH.ParensE (patToExp p)
    patToExp (TH.TildeP p) = patToExp p
    patToExp (TH.BangP p) = patToExp p
    patToExp TH.WildP = TH.TupE []
    patToExp (TH.RecP n fs) = TH.RecConE n $ map (second patToExp) fs
    patToExp (TH.ListP ps) = TH.ListE (map patToExp ps)
    patToExp (TH.SigP p t) = TH.SigE (patToExp p) t
    patToExp p = error $ "branch: Not supported: " ++ pprint p

    makeForward' :: TH.Pat -> [TH.Name] -> Q TH.Exp
    makeForward' pat0 vs = do
      let e = return $ foldr (\a r -> TH.TupE [TH.VarE a, r]) (TH.TupE []) vs
      [|\x -> case x of $(return pat0) -> Just $(e); _ -> Nothing|]

    makeBackward' :: TH.Pat -> [TH.Name] -> Q TH.Exp
    makeBackward' pat0 vs = do
      let p = return $ foldr (\a r -> TH.TupP [TH.VarP a, r]) (TH.TupP []) vs
      [|\ $(p) -> Just $(return $ patToExp pat0)|]

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
numberOfArgs _                               = 0

makeForward :: TH.Name -> Int -> Bool -> Q TH.Exp
makeForward cn n isSing = do
  vs <- mapM (\i -> TH.newName ("x" ++ show i)) [1 .. n]
  let p = return $ TH.ConP cn $ map TH.VarP vs
  let exp = return $ foldr (\x r -> TH.TupE [TH.VarE x, r]) (TH.TupE []) vs
  if isSing
    then [|\ $(p) -> Just $(exp)|]
    else [|\x -> case x of $(p) -> Just $(exp); _ -> Nothing|]

makeBackward :: TH.Name -> Int -> Q TH.Exp
makeBackward cn n = do
  vs <- mapM (\i -> TH.newName ("x" ++ show i)) [1 .. n]
  let p = return $ foldr (\x r -> TH.TupP [TH.VarP x, r]) (TH.TupP []) vs
  let exp = return $ foldl TH.AppE (TH.ConE cn) $ map TH.VarE vs
  [|\ $(p) -> Just $(exp)|]

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
