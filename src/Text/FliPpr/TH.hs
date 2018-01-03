{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TemplateHaskell #-}

module Text.FliPpr.TH where

import Text.FliPpr.Internal.Type

import Language.Haskell.TH as TH

{- |

-}
un :: TH.Name -> Q TH.Exp
un cname = do
  cinfo <- TH.reify cname
  case cinfo of
    TH.DataConI _ ty tyname -> do 
      let n   = numberOfArgs ty
      isSing <- isSingleton tyname 
      let f   = makeForward  cname n isSing
      let fi  = makeBackward cname n 
      let exp = makeBody n 
      [| \e ->
          PInv $(TH.litE $ TH.stringL $ TH.nameBase cname) $f $fi
        `Branch`
        $(exp) e |]
    _ ->
      fail $ "un: " ++ show cname ++ " is not a constructor" 
  where
    isSingleton :: TH.Name -> Q Bool
    isSingleton tyname = do
      info <- TH.reify tyname
      case info of        
        TH.TyConI dec -> 
          case dec of
            TH.DataD _ _ _ _ cs _ ->
              return $ length cs <= 1
            TH.NewtypeD _ _ _ _ _ _ ->
              return True
            TH.DataInstD _ _ _ _ cs _ ->
              return $ length cs <= 1
            TH.NewtypeInstD _ _ _ _ _ _ ->
              return True
            _ ->
              return False 
        _ ->
          return False
          
    numberOfArgs :: TH.Type -> Int
    numberOfArgs (TH.AppT (TH.AppT ArrowT _) t2) = numberOfArgs t2 + 1
    numberOfArgs (TH.ForallT _ _ t)              = numberOfArgs t
    numberOfArgs (TH.SigT t _)                   = numberOfArgs t
    numberOfArgs (TH.ParensT t)                  = numberOfArgs t
    numberOfArgs _                               = 0 
    
    makeForward :: TH.Name -> Int -> Bool -> Q TH.Exp
    makeForward cname n isSing = do
      vs <- mapM (\i -> TH.newName ("x" ++ show i)) [1..n]
      let pat = return $ TH.ConP cname $ map TH.VarP vs
      let exp = return $ foldr (\x r -> TH.TupE [TH.VarE x,r]) (TH.TupE []) vs
      if isSing
        then [| \ $( pat ) -> Just $( exp ) |]
        else [| \ x -> case x of { $( pat ) -> Just $( exp ); _ -> Nothing } |]

    makeBackward :: TH.Name -> Int -> Q TH.Exp
    makeBackward cname n = do
      vs <- mapM (\i -> TH.newName ("x" ++ show i)) [1..n]
      let pat = return $ foldr (\x r -> TH.TupP [TH.VarP x,r]) (TH.TupP []) vs
      let exp = return $ foldl TH.AppE (TH.ConE cname) $ map TH.VarE vs
      [| \ $( pat ) -> Just $( exp ) |]
  
    makeBody :: Int -> Q TH.Exp
    makeBody n = do
      vs <- mapM (\i -> TH.newName ("x" ++ show i)) [1..n]
      x  <- TH.newName "_u"
      z  <- TH.newName "z" 
      [| \ $( TH.varP z ) $( TH.varP x ) -> $( go vs vs x z ) |]
        where
          go []     ovs _ z = return $ foldl TH.AppE (TH.VarE z) $ map TH.VarE ovs 
          go (v:vs) ovs x z = do
            x' <- TH.newName "_u"
            [| unpair $( TH.varE x) $
                 \ $( TH.varP v ) $( TH.varP x' ) -> $(go vs ovs x' z) |]

{- |
A syntactic sugar for 'Branch'. 
A typical usage is:

@@
 $(branch [p| a : x |] [| ppr `app` a <> pprs `app` x |])
@@

The variables in the pattern must be different from any other bound variable in the scope.
Otherwise, the same variable in the body refers to the bound variable,
instead of the one introduced in the pattern. 
-}
branch :: Q (TH.Pat) -> Q (TH.Exp) -> Q (TH.Exp)
branch patQ expQ = do
  pat <- patQ
  exp <- expQ
  let vs = gatherVarNames pat
  let f  = makeForward  pat vs
  let fi = makeBackward pat vs 
  let nf = "<" ++ pprint pat ++ ">"
  [| Branch (PInv $(TH.litE $ TH.stringL $ nf) $f $fi)
     $(makeBody exp vs) |]
    where
      gatherVarNames :: TH.Pat -> [TH.Name]
      gatherVarNames = flip go []
        where
          go (TH.LitP _)          r = r
          go (TH.VarP n)          r = n:r
          go (TH.TupP ps)         r = foldr ($) r (map go ps) 
          go (TH.UnboxedTupP ps)  r = foldr ($) r (map go ps)
          go (TH.ConP _ ps)       r = foldr ($) r (map go ps)
          go (TH.InfixP p1 _ p2)  r = go p1 (go p2 r)
          go (TH.UInfixP p1 _ p2) r = go p1 (go p2 r)
          go (TH.ParensP p)       r = go p r
          go (TH.TildeP p )       r = go p r
          go (TH.BangP p)         r = go p r
          go (TH.WildP)           r = r
          go (TH.RecP _ fs)       r = foldr ($) r (map (go . snd) fs)
          go (TH.ListP ps)        r = foldr ($) r (map go ps)
          go (TH.SigP p _)        r = go p r
          go p _                    = error $ "branch: Not supported: " ++ pprint p 

      patToExp :: TH.Pat -> TH.Exp
      patToExp (TH.LitP l)          = TH.LitE l
      patToExp (TH.VarP x)          = TH.VarE x
      patToExp (TH.TupP ps)         = TH.TupE (map patToExp ps)
      patToExp (TH.UnboxedTupP ps)  = TH.UnboxedTupE (map patToExp ps)
      patToExp (TH.ConP c ps)       = foldl (TH.AppE) (TH.ConE c) $ map patToExp ps
      patToExp (TH.InfixP p1 n p2)  = TH.InfixE (Just $ patToExp p1) (TH.ConE n) (Just $ patToExp p2)
      patToExp (TH.UInfixP p1 n p2) = TH.UInfixE (patToExp p1) (TH.ConE n) (patToExp p2)
      patToExp (TH.ParensP p)       = TH.ParensE (patToExp p)
      patToExp (TH.TildeP p)        = patToExp p
      patToExp (TH.BangP  p)        = patToExp p
      patToExp (TH.WildP)           = TH.TupE []
      patToExp (TH.RecP n fs)       = TH.RecConE n $ map (\(n,p) -> (n, patToExp p)) fs
      patToExp (TH.ListP ps)        = TH.ListE (map patToExp ps)
      patToExp (TH.SigP p t)        = TH.SigE (patToExp p) t
      patToExp p                    = error $ "branch: Not supported: " ++ pprint p 

      makeForward :: TH.Pat -> [TH.Name] -> Q TH.Exp 
      makeForward pat vs = do
        let e = return $ foldr (\a r -> TH.TupE [a,r]) (TH.TupE []) $ map TH.VarE vs
        [| \x -> case x of { $( return pat ) -> Just $( e ); _ -> Nothing } |]

      makeBackward :: TH.Pat -> [TH.Name] -> Q TH.Exp 
      makeBackward pat vs = do
        let p = return $ foldr (\a r -> TH.TupP [a,r]) (TH.TupP []) $ map TH.VarP vs
        [| \ $( p ) -> Just $( return $ patToExp pat ) |]

      makeBody :: TH.Exp -> [TH.Name] -> Q TH.Exp
      makeBody exp vs = do
        x  <- TH.newName "_u"
        [| \ $( TH.varP x ) -> $( go vs x ) |]
          where
            go []     _ = return $ exp
            go (u:us) x = do
              x' <- TH.newName "_u"
              [| unpair $( TH.varE x) $
                 \ $( TH.varP u ) $( if null vs then TH.wildP else TH.varP x' ) -> $(go us x') |]
