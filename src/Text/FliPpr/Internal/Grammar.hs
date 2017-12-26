{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -fprint-explicit-kinds #-}

module Text.FliPpr.Internal.Grammar where

import Text.FliPpr.Internal.Env as E

import Text.FliPpr.Internal.Type as T (Rec(..))
import Text.FliPpr.Container2 as T
import Text.FliPpr.Internal.CPS 

import Text.FliPpr.Doc as D 

import Data.Typeable ((:~:)(Refl))
import Data.List     (sortBy)

import Prelude hiding ((.), id)
import Control.Category ((.), id) 
import Control.Applicative as A (Alternative(..)) 
import Data.Coerce 

import Text.FliPpr.Internal.Grammar.Type as G


import Debug.Trace


{-
Reduce a grammar, with a simple inlining 
-}

newtype RedMap env new =
  RedMap { runRedMap :: forall a. V env a -> Maybe (V new a) }

insert :: VT new new' -> V env a -> V new' a -> RedMap env new -> RedMap env new'
insert vt x y m = RedMap $ \x' ->
  case E.eqVar x' x of
    Just Refl -> Just y
    Nothing   -> fmap (shift vt) (runRedMap m x')
  

newtype Tr m rhs res a =
  Tr { runTr :: forall old.
                m old -> E' rhs old -> TrR m rhs res old a }

data TrR m rhs res old a =
  forall new. TrR (FreeA res new a) (m new) (E' rhs new)  (VT old new)

toGrammar :: Tr m (OpenRHS c) (OpenRHS c) a -> m '[] -> Grammar c a
toGrammar (Tr k) m0 =
  case k m0 E.emptyEnv of
    TrR ps _ env _ ->
      case unFree ps of
        RSingle (PSymb (NT x)) ->
          Grammar x (mapEnv finalizeRHS env)
        _ -> 
          let (env1, r1, _) = E.extendEnv' env (unFree ps)
          in Grammar r1 (mapEnv finalizeRHS env1) 
  

data FreeA f n a where
  FPure :: a -> FreeA f n a
  FMult :: FreeA f n (a -> b) -> FreeA f n a -> FreeA f n b
  FRaw  :: f n a -> FreeA f n a 
    
instance Functor (FreeA f n) where
  fmap f x = pure f <*> x 

instance Applicative (FreeA f n) where
  pure  = FPure
  (<*>) = FMult

unFree :: Applicative (f n) => FreeA f n a -> f n a
unFree (FPure a)   = pure a
unFree (FMult f a) = unFree f <*> unFree a 
unFree (FRaw  x)   = x 

instance Shiftable d f => Shiftable d (FreeA f) where
  shift _  (FPure a)   = FPure a
  shift vt (FMult f a) = FMult (shift vt f) (shift vt a)
  shift vt (FRaw x)    = FRaw (shift vt x) 
  
instance Functor (Tr m rules res) where
  fmap f (Tr k) = Tr $ \m env -> case k m env of
    TrR res m' env' vt' -> TrR (fmap f res) m' env' vt'

instance Shiftable EnvRep res => Applicative (Tr m rules res) where
  pure a = Tr $ \m env -> TrR (pure a) m env id
  Tr f <*> Tr a = Tr $ \m env ->
    case f m env of
      TrR res1 m1 env1 vt1 ->
        case a m1 env1 of
          TrR res2 m2 env2 vt2 ->
            TrR (shift vt2 res1 <*> res2) m2 env2 (vt2 . vt1)

type TrG c m a = Tr m (OpenRHS c) (OpenRHS c) a 
  
prodOpt :: (forall env env'. VT env env' -> m env -> m env') ->
           TrG c m (a -> b) -> TrG c m a -> TrG c m b 
prodOpt shifter (Tr f) (Tr a) = Tr $ \m env ->
  case f m env of
    TrR fres1 m1 env1 vt1 ->
      case a m1 env1 of
        TrR fres2 m2 env2 vt2 ->
          let res1 = unFree fres1
              res2 = unFree fres2
          in if atmostSingle res1 || atmostSingle res2 then
               TrR (FRaw (shift vt2 res1 <*> res2))
                   m2
                   env2
                   (vt2 . vt1)
          else
            case G.shareRHS (shift vt2 res1) env2 of
              ResultG res1' env3 vt3 ->
                case G.shareRHS (shift vt3 res2) env3 of
                  ResultG res2' env4 vt4 ->
                    TrR (FRaw (shift vt4 res1' <*> res2'))
                        (shifter (vt4 . vt3) m2)
                        env4
                        (vt4 . vt3 . vt2 . vt1)


makeAlt :: TrG c m a -> TrG c m a -> TrG c m a
makeAlt (Tr a) (Tr b) = Tr $ \m env ->
  case a m env of
    TrR res1 m1 env1 vt1 ->
      case b m1 env1 of
        TrR res2 m2 env2 vt2 -> 
          TrR (FRaw $ unFree (shift vt2 res1) `G.runion` unFree res2) m2 env2 (vt2 . vt1)

makeEmpty :: TrG c m a
makeEmpty = Tr $ \m env -> TrR (FRaw $ REmpty) m env id 

makeAlts :: [TrG c m a] -> TrG c m a
makeAlts []     = makeEmpty
makeAlts [a]    = a
makeAlts (a:as) = a `makeAlt` makeAlts as 

tryDiscard :: Maybe (a :~: ()) -> TrG c m a -> TrG c m a
tryDiscard Nothing x = x
tryDiscard (Just Refl) (Tr a) = Tr $ \m env ->
  case a m env of
    TrR res1 m1 env1 vt1 -> TrR (FRaw $ RVoid $ unFree res1) m1 env1 vt1 

reduce :: Grammar c a -> Grammar c a
reduce (Grammar v oldEnv) =
  toGrammar (work (E.lookupEnv v oldEnv) oldEnv) (RedMap $ const Nothing) 
  where
    -- TODO: The current implementation is a bit too conservative
    -- in inlining. It would generate a grammar with the rules of the form
    -- of Pk = Pj.

    work :: RHS c env a -> E' (RHS c) env -> TrG c (RedMap env) a
    work (RHS ss b) oldRules =
      tryDiscard b $ makeAlts (map (\s -> workProd s oldRules) ss)

    workProd :: Prod c env a -> E' (RHS c) env -> TrG c (RedMap env) a
    workProd (PNil a)    _oldRules = pure a
    workProd (PCons a f)  oldRules =
      makeProd (fmap (\a k -> k a) (workSymb a oldRules)) (workProd f oldRules)

    makeProd = prodOpt shifter
      where
        shifter vt m = RedMap $ fmap (shift vt) . runRedMap m 

    workSymb :: Symb c env a -> E' (RHS c) env -> TrG c (RedMap env) a
    workSymb (NT x) oldRules = Tr $ \m e ->
      case runRedMap m x of
        Just v -> TrR (FRaw $ RSingle (PSymb (NT v))) m e id
        Nothing ->
          let ps = E.lookupEnv x oldRules
          in if inlinable ps then
               runTr (work ps oldRules) m e
             else 
               let (env1, r1, vt1) = E.extendEnv' e RUnInit 
                   m' = insert vt1 x r1 m 
               in case runTr (work ps oldRules) m' env1 of
                    TrR fps2 m2 env2 vt2 ->
                      let ps2   = unFree fps2
                          env2' = E.updateEnv (shift vt2 r1) ps2 env2
                      in TrR (FRaw $ RSingle $ PSymb $ NT $ shift vt2 r1) m2 env2' (vt2 . vt1)

    workSymb (TermC c) _oldRules =
      Tr $ \m e -> TrR (FRaw $ RSingle (PSymb (TermC c))) m e id 
    workSymb (TermP c) _oldRules =
      Tr $ \m e -> TrR (FRaw $ RSingle (PSymb (TermP c))) m e id 
    -- workSymb Space _oldRules =
    --   Tr $ \m e -> TrR (FRaw $ RSingle (PSymb Space)) m e id 
    -- workSymb Spaces _oldRules =
    --   Tr $ \m e -> TrR (FRaw $ RSingle (PSymb Spaces)) m e id 

    inlinable :: RHS c env a -> Bool
    inlinable (RHS [] _)  = True
    inlinable (RHS [s] _) = isConstant s || isDirect s 
    inlinable _           = False

    isDirect (PNil _) = True
    isDirect (PCons (NT _) (PNil _)) = True
    isDirect _ = False 

    isConstant :: Prod c env a -> Bool
    isConstant (PNil _) = True
    isConstant (PCons s r) =
      nonNT s && isConstant r
      where
        nonNT (NT _) = False
        nonNT _      = True 
          

type Q = Int
data Transducer inc outc =
  Transducer Q                     -- ^ init state
             [Q]                   -- ^ all the states
             [Q]                   -- ^ final states
             (Trans inc outc)

data Trans inc outc = Trans (Q -> inc -> ([outc], Q)) -- ^ transitions
                            (Q -> Maybe [outc])             -- ^ final rules 

finalProd :: Q -> Trans inc outc -> Maybe [outc]
finalProd q (Trans _ f) = f q 


transTo :: Q -> inc -> Trans inc outc -> ([outc], Q)
transTo qi c (Trans tr _) = tr qi c 

newtype ProdMap env new =
  ProdMap { runProdMap :: forall a. V env a -> Q -> Q -> Maybe (V new a) }


productConstruction :: Grammar inc a -> Transducer inc outc -> Grammar outc a
productConstruction (Grammar var env) (Transducer start states finals tr) =
  toGrammar  
  (makeAlts [ fmap (\a _ -> a) (goRHS (E.lookupEnv var env) env start fin tr) `makeProd` fromList os
            | fin <- finals, os <- maybe [] (:[]) (finalProd fin tr) ])
  (ProdMap $ \_ _ _ -> Nothing) 
  where
    fromList []     = pure []
    fromList (c:cs) = fmap (:) (fromTerm c) `makeProd` fromList cs

    fromTerm c = Tr $ \m e -> TrR (FRaw $ RSingle (PSymb (TermC c))) m e id
--    fromCond c = Tr $ \m e -> TrR (FRaw $ RSingle (PSymb (TermP c))) m e id

    makeProd = prodOpt shifter
      where
        shifter vt m = ProdMap $ \v q q' -> fmap (shift vt) (runProdMap m v q q')
    
    goRHS :: RHS inc env a -> E' (RHS inc) env -> Q -> Q -> Trans inc outc -> TrG outc (ProdMap env) a
    goRHS (RHS ps b) oldRules q q' tr = 
      tryDiscard b $ makeAlts $ map (\p -> goProd p oldRules q q' tr) ps

    goProd :: Prod inc env a -> E' (RHS inc) env -> Q -> Q -> Trans inc outc -> TrG outc (ProdMap env) a
    goProd (PNil  ret) _ q q' _ = if q == q' then
                                    pure ret
                                  else
                                    makeEmpty

    goProd (PCons (TermC c) rest) oldRules q q' tr =
      let (os, qo) = transTo q c tr
      in fmap (\_ k -> k c) (fromList os) `makeProd` goProd rest oldRules qo q' tr
    goProd (PCons (NT x) rest) oldRules q q' tr =
      makeAlts [ fmap (\a k -> k a) (goNT x oldRules q qm tr) `makeProd` goProd rest oldRules qm q' tr | qm <- states ]
    goProd (PCons (TermP _c) _rest) _oldRules _q _q' _tr =
      error "Not implemented yet" 


    goNT :: V env a -> E' (RHS inc) env -> Q -> Q -> Trans inc outc -> TrG outc (ProdMap env) a
    goNT x oldRules q q' tr = Tr $ \m e -> 
      case runProdMap m x q q' of
        Just v ->
          TrR (FRaw $ RSingle (PSymb (NT v))) m e id
        Nothing ->
          let ps = E.lookupEnv x oldRules
              (env1, r1, vt1) = E.extendEnv' e RUnInit 
              m' = ProdMap $ \v qq qq' ->
                              case E.eqVar v x of
                                Just Refl | qq == q && qq' == q' ->  Just r1
                                _                                ->  fmap (shift vt1) (runProdMap m v qq qq')
          in case runTr (goRHS ps oldRules q q' tr) m' env1 of
               TrR fps2 m2 env2 vt2 ->
                 let ps2   = unFree fps2
                     env2' = E.updateEnv (shift vt2 r1) ps2 env2
                 in TrR (FRaw $ RSingle $ PSymb $ NT $ shift vt2 r1) m2 env2' (vt2 . vt1)

newtype Flag env a = Flag Bool 
-- data TrP c old = TrP (forall env. E' (RHS c) env -> VT old env ->
--                        exists env'. (RHS c env', VT old env', E' (RHS c) en'v))

-- type TrP c orig a = Tr (VT orig) (OpenRHS c) (OpenRHS c) a

instance Pretty (Flag env a) where
  ppr (Flag b) = D.text "Flag" D.<+> ppr b 

instance Pretty (E' Flag env) where
  ppr = E.pprEnv (\_ -> ppr) (D.text "P")

filterProductive :: Grammar c a -> Grammar c a
filterProductive (Grammar x env) =
  let m = loop (E.mapEnv (const $ Flag False) env) env 
  in trace (show $ D.ppr m) $ toGrammar (goRHS m env (E.lookupEnv x env)) (RedMap $ const Nothing)
  where
    goRHS :: E' Flag orig -> E' (RHS c) orig -> RHS c orig a -> TrG c (RedMap orig) a
    goRHS m orules (RHS ss w) =
      tryDiscard w $ makeAlts $ map (\s -> goProd m orules s) ss 

    goProd :: E' Flag orig -> E' (RHS c) orig -> Prod c orig a -> TrG c (RedMap orig) a
    goProd _ _ (PNil a) = pure a
    goProd m orules (PCons a r) =
      fmap (\a k -> k a) (goSymb m orules a) `makeProd` goProd m orules r

    makeProd = prodOpt shifter
      where
        shifter vt m = RedMap $ fmap (shift vt) . runRedMap m 

    goSymb :: E' Flag orig -> E' (RHS c) orig -> Symb c orig a -> TrG c (RedMap orig) a
    goSymb _ _ (TermC c) =
      Tr $ \m e -> TrR (FRaw $ RSingle (PSymb (TermC c))) m e id
    goSymb _ _ (TermP c) =
      Tr $ \m e -> TrR (FRaw $ RSingle (PSymb (TermP c))) m e id
    goSymb m orules (NT x)
      | coerce (E.lookupEnv x m) = Tr $ \tb env ->
        case runRedMap tb x of
          Just v -> TrR (FRaw $ RSingle (PSymb (NT v))) tb env id
          Nothing ->
            let r = E.lookupEnv x orules
            in if inlinable r then
                 runTr (goRHS m orules r) tb env 
               else 
                 let (env1, x1, vt1) = E.extendEnv' env RUnInit
                     tb' = insert vt1 x x1 tb 
                 in case runTr (goRHS m orules r) tb' env1 of
                   TrR r2 tb2 env2 vt2 ->
                     let env2' = E.updateEnv (shift vt2 x1) (unFree r2) env2
                     in TrR (FRaw $ RSingle $ PSymb $ NT $ shift vt2 x1) tb2 env2' (vt2 . vt1)
      | otherwise =
          makeEmpty 
      

    inlinable :: RHS c env a -> Bool
    inlinable (RHS [] _)  = True
    inlinable (RHS [s] _) = isConstant s || isDirect s 
    inlinable _           = False

    isDirect (PNil _) = True
    isDirect (PCons (NT _) (PNil _)) = True
    isDirect _ = False 

    isConstant :: Prod c env a -> Bool
    isConstant (PNil _) = True
    isConstant (PCons s r) =
      nonNT s && isConstant r
      where
        nonNT (NT _) = False
        nonNT _      = True 
      
    loop :: E' Flag env -> E' (RHS c) env -> E' Flag env 
    loop m env =
      let m' = update m env
      in if eqFlag m m' then m' else loop m' env

    eqFlag :: E' Flag env -> E' Flag env -> Bool 
    eqFlag m m' =
      foldrEnv (\(Flag b) r -> b && r) True $ E.zipWithEnv (\(Flag b) (Flag b') -> Flag (b == b')) m m' 

    update :: E' Flag env -> E' (RHS c) env -> E' Flag env
    update m env = E.zipWithEnv (check m) m env
      where
        check :: E' Flag env -> Flag env a -> RHS c env a -> Flag env a
        check m (Flag b) (RHS ss _) =
          if b then Flag True 
          else      Flag $ or $ map (checkProd m) ss

        checkProd :: E' Flag env -> Prod c env a -> Bool
        checkProd _ (PNil _)    = True
        checkProd m (PCons c r) = checkSymb m c && checkProd m r

        checkSymb :: E' Flag env -> Symb c env a -> Bool
        checkSymb m (NT x) = coerce $ E.lookupEnv x m          
        checkSymb _ _      = True

          


optSpaces :: Grammar ExChar a -> Grammar ExChar a
optSpaces g = productConstruction (normalize g) tr 
  where 
    tr = Transducer 0 [0,1,2] [0,1,2] (Trans trC trF)
    trC 0 Space  = ([], 1)
    trC 0 Spaces = ([], 2)
    trC 0 (NormalChar c) = ([NormalChar c], 0)

    trC 1 Space  = ([Space], 1)
    trC 1 Spaces = ([Space], 2)
    trC 1 (NormalChar c) = ([Space, NormalChar c], 0)

    trC 2 Space  = ([Space],  2)
    trC 2 Spaces = ([],       2)
    trC 2 (NormalChar c) = ([Spaces, NormalChar c], 0)

    trC _ _ = error "Cannot happen"

    trF 0 = Just []
    trF 1 = Just [Space]
    trF 2 = Just [Spaces]
    trF _ = error "Cannot happen" 

    normalize :: Grammar ExChar a -> Grammar ExChar a
    normalize (Grammar x env) = Grammar x (E.mapEnv norm env)

    norm :: RHS ExChar env a -> RHS ExChar env a
    norm (RHS ss Nothing)     = RHS ss Nothing
    norm (RHS ss (Just Refl)) = RHS (norm' False $ sortBy cmp ss) (Just Refl)
      where
        cmp :: Prod ExChar env a -> Prod ExChar env b -> Ordering
        cmp (PNil _) (PCons _ _)    = LT
        cmp (PNil _) (PNil _)       = EQ 
        cmp (PCons _ _) (PNil _)    = GT
        cmp (PCons _ a) (PCons _ b) = cmp a b 

    norm' :: Bool -> [Prod ExChar env ()] -> [Prod ExChar env ()]
    norm' _ (PNil _:ss) = norm' True ss
    norm' True (PCons (TermC Space) (PCons (TermC Spaces) (PNil _)):ss) = PCons (TermC Spaces) (PNil $ const ()):norm' True ss
    norm' b (s:ss) = s:norm' b ss
    norm' b [] = if b then [PNil ()] else [] 
      



example1 :: Grammar ExChar ()
example1 = finalize $ G.fix1 $ \p ->
  () <$ G.text "(" <* p <* G.text ")" <* p
  <|> pure () 
  
                               
example2 :: Grammar ExChar ()
example2 = finalize $
  let f (a,b) =
        (() <$ alphas <* G.spaces <* G.text "[" <* G.spaces <* b <* G.text "]",
         () <$ a <* G.spaces <* G.text "," <* G.spaces <* b 
         <|> () <$ a
         <|> pure ())
  in G.fix1 $ \x -> fst (f (x, G.fix1 $ \y -> snd (f (x,y))))
  where
    alpha = G.fix1 $ \_ ->
      foldr1 (<|>) $ map G.char ['a'..'z']                               
    alphas = G.fix1 $ \p ->
      (:) <$> alpha <*> p <|> (:[]) <$> alpha 


example3 :: Grammar ExChar ()
example3 = finalize $ unCPS $ do 
  alpha  <- G.share $ foldr1 (<|>) $ map G.char ['a'..'z']
  alphas <- G.share $ G.fix1 $ \p -> (:) <$> alpha <*> p
                                     <|> (:[]) <$> alpha
  (tree :< _) <- G.fixn $
    Rec (\(_ :< forest :< _) ->
            () <$ alphas <* G.spaces <* G.text "[" <* G.spaces <* forest <* G.text "]")
    :<
    Rec (\(tree :< forest :< _) ->
            () <$ tree <* G.spaces <* G.text "," <* G.spaces <* forest
          <|> () <$ tree 
          <|> pure ())
    :< End
  return tree 
  
{-
Implementing mutual recursions by Bekic's lemma causes grammar-size blow-up.
-} 
example4 :: Grammar ExChar ()
example4 = finalize $
  let f (a,b) =
        (() <$ alphas <* G.spaces <* G.text "[" <* G.spaces <* b <* G.text "]",
         () <$ a <* G.spaces <* G.text "," <* G.spaces <* b 
         <|> () <$ a
         <|> pure ())
      p1 = G.fix1 $ \x -> fst (f (x, G.fix1 $ \y -> snd (f (x,y))))
      p2 = G.fix1 $ \y -> snd (f (G.fix1 $ \x -> fst (f (x,y)), y))
  in p1 <|> p2 
  where
    alpha = G.fix1 $ \_ ->
      foldr1 (<|>) $ map G.char ['a'..'z']                               
    alphas = G.fix1 $ \p ->
      (:) <$> alpha <*> p <|> (:[]) <$> alpha 

-- sample4 :: Grammar ()
-- sample4 = finalize $
--   let f (a,b) =
--         (() <$ alphas <* G.spaces <* G.text "[" <* b <* G.text "]",
--          () <$ a <* G.spaces <* G.text "," <* G.spaces <* b 
--          <|> () <$ a
--          <|> pure ())
--   in gfix2 f (\(p1,p2) -> p1 <|> p2)
--   where
--     alpha = G.fix1 $ \p ->
--       foldr1 (<|>) $ map G.char ['a'..'z']                               
--     alphas = G.fix1 $ \p ->
--       (:) <$> alpha <*> p <|> pure []

example5 :: Grammar ExChar ()
example5 = finalize $ unCPS $ do
  alpha  <- G.share $ foldr1 (<|>) $ map G.char ['a'..'z']
  alphas <- G.share $ G.fix1 $ \p ->
    (:) <$> alpha <*> p
    <|> (:[]) <$> alpha 
  let f (a,b) =
        (() <$ alphas <* G.spaces <* G.text "[" <* G.spaces <* b <* G.text "]",
         () <$ a <* G.spaces <* G.text "," <* G.spaces <* b 
         <|> () <$ a
         <|> pure ())
  (p1 :< p2 :< _) <- G.fixn $
       (Rec $ \(g1 :< g2 :< _) -> fst $ f (g1, g2))
       :<
       (Rec $ \(g1 :< g2 :< _) -> snd $ f (g1, g2))
       :<
       End
  return $ p1 <|> p2 
      -- ((\(a :> b :> End) -> let (a',b') = f (a,b)
      --                       in a' :> b' :> End)
      --  :: Apps GrammarUC [(), ()] -> Apps GrammarUC [(), ()])
      -- (\(p1 :> p2 :> End) -> p1 <|> p2)

-- similar, but alls are defined via gfixn 
example6 :: Grammar ExChar ()
example6 = finalize $ unCPS $ do
  (_ :< _ :< tree :< forest :< _) <- G.fixn $
    (Rec $ \_ -> foldr1 (<|>) $ map G.char ['a'..'z'])
    :<
    (Rec $ \(alpha :< alphas :< _) ->
        (:) <$> alpha <*> alphas <|> (:[]) <$> alpha)
    :<
    (Rec $ \(_ :< alphas :< _ :< forest :< _) ->
        () <$ alphas <* G.spaces <* G.text "[" <* G.spaces <* forest <* G.text "]")
    :<
    (Rec $ \(_ :< _ :< tree :< forest :< _) ->
         () <$ tree <* G.spaces <* G.text "," <* G.spaces <* forest
         <|> () <$ tree <|> pure () )
    :< End
  return $ tree <|> forest
    
        
  -- gfixn ((\(alpha :> alphas :> tree :> forest :> End) ->
  --            (foldr1 (<|>) $ map G.char ['a'..'z']) :>
  --            ( (:) <$> alpha <*> alphas <|> pure [] ) :>
  --            ( () <$ alphas <* G.spaces <* G.text "[" <* forest <* G.text "]") :>
  --            ( () <$ tree <* G.spaces <* G.text "," <* G.spaces <* forest
  --              <|> () <$ tree <|> pure () ) :> End)
  --         :: Apps GrammarUC [Char, String, (), ()]
  --            -> Apps GrammarUC [Char, String, (), ()])
  --        (\(_ :> _ :> tree :> forest :> End) -> tree <|> forest)

        
