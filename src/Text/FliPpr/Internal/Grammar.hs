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

import Data.Typeable ((:~:)(Refl))
import Prelude hiding ((.), id)
import Control.Category ((.), id) 
import Control.Applicative as A (Alternative(..)) 

import Text.FliPpr.Internal.Grammar.Type as G

import Debug.Trace

{-
Reduce a grammar, with a simple inlining 
-}

newtype RedMap env new =
  RedMap { runRedMap :: forall a. V env a -> Maybe (V new a) }

newtype Tr m rhs res a =
  Tr { runTr :: forall old.
                m old -> E' rhs old -> TrR m rhs res old a }

data TrR m rhs res old a =
  forall new. TrR (FreeA res new a) (m new) (E' rhs new)  (VT old new)

toGrammar :: Tr m (OpenRHS c) (OpenRHS c) a -> m '[] -> Grammar c a
toGrammar (Tr k) m0 =
  case k m0 E.emptyEnv of
    TrR ps _ env _ ->
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


reduce :: Grammar c a -> Grammar c a
reduce (Grammar v oldEnv) =
  toGrammar (work (E.lookupEnv v oldEnv) oldEnv) (RedMap $ const Nothing) 
  where
    -- TODO: The current implementation is a bit too conservative
    -- in inlining. It would generate a grammar with the rules of the form
    -- of Pk = Pj.

    work :: RHS c env a -> E' (RHS c) env -> TrG c (RedMap env) a
    work (RHS [])     _oldRules = Tr $ \m e -> TrR (FRaw REmpty) m e id
    work (RHS [s])     oldRules = workProd s oldRules 
    work (RHS (s:ss))  oldRules =
      makeAlt (workProd s oldRules) (work (RHS ss) oldRules) 

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
                   m' = RedMap $ \v ->
                     case E.eqVar v x of
                       Just Refl ->  Just r1
                       Nothing   ->  fmap (shift vt1) (runRedMap m v)
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
    inlinable (RHS [])  = True
    inlinable (RHS [s]) = isConstant s
    inlinable _         = False

    isConstant :: Prod c env a -> Bool
    isConstant (PNil _) = True
    isConstant (PCons s r) =
      nonNT s && isConstant r
      where
q        nonNT (NT _) = False
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
  (alts [ fmap (\a _ -> a) (goRHS (E.lookupEnv var env) env start fin tr) `makeProd` fromList os
        | fin <- finals, os <- maybe [] (:[]) (finalProd fin tr) ])
  (ProdMap $ \_ _ _ -> Nothing) 
  where
    fromList []     = pure []
    fromList (c:cs) = fmap (:) (fromTerm c) `makeProd` fromList cs

    fromTerm c = Tr $ \m e -> TrR (FRaw $ RSingle (PSymb (TermC c))) m e id
--    fromCond c = Tr $ \m e -> TrR (FRaw $ RSingle (PSymb (TermP c))) m e id

    alts []     = makeEmpty
    alts [a]    = a
    alts (a:as) = makeAlt a (alts as) 

    makeProd = prodOpt shifter
      where
        shifter vt m = ProdMap $ \v q q' -> fmap (shift vt) (runProdMap m v q q')
    
    goRHS :: RHS inc env a -> E' (RHS inc) env -> Q -> Q -> Trans inc outc -> TrG outc (ProdMap env) a
    goRHS (RHS ps) oldRules q q' tr = 
      alts $ map (\p -> goProd p oldRules q q' tr) ps

    goProd :: Prod inc env a -> E' (RHS inc) env -> Q -> Q -> Trans inc outc -> TrG outc (ProdMap env) a
    goProd (PNil  ret) _ q q' _ = if q == q' then
                                    pure ret
                                  else
                                    makeEmpty

    goProd (PCons (TermC c) rest) oldRules q q' tr =
      let (os, qo) = transTo q c tr
      in fmap (\_ k -> k c) (fromList os) `makeProd` goProd rest oldRules qo q' tr
    goProd (PCons (NT x) rest) oldRules q q' tr =
      alts [ fmap (\a k -> k a) (goNT x oldRules q qm tr) `makeProd` goProd rest oldRules qm q' tr | qm <- states ]
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

optSpaces :: Grammar ExChar a -> Grammar ExChar a
optSpaces g = productConstruction g tr
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
  



example1 :: Grammar ExChar ()
example1 = finalize $ G.fix1 $ \p ->
  () <$ G.text "(" <* p <* G.text ")" <* p
  <|> pure () 
  
                               
example2 :: Grammar ExChar ()
example2 = finalize $
  let f (a,b) =
        (() <$ alphas <* G.spaces <* G.text "[" <* b <* G.text "]",
         () <$ a <* G.spaces <* G.text "," <* G.spaces <* b 
         <|> () <$ a
         <|> pure ())
  in G.fix1 $ \x -> fst (f (x, G.fix1 $ \y -> snd (f (x,y))))
  where
    alpha = G.fix1 $ \_ ->
      foldr1 (<|>) $ map G.char ['a'..'z']                               
    alphas = G.fix1 $ \p ->
      (:) <$> alpha <*> p <|> pure []

{-
Implementing mutual recursions by Bekic's lemma causes grammar-size blow-up.
-} 
example3 :: Grammar ExChar ()
example3 = finalize $
  let f (a,b) =
        (() <$ alphas <* G.spaces <* G.text "[" <* b <* G.text "]",
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
      (:) <$> alpha <*> p <|> pure []

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
  let f (a,b) =
        (() <$ alphas <* G.spaces <* G.text "[" <* b <* G.text "]",
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
  where
    alpha = G.fix1 $ \_ ->
      foldr1 (<|>) $ map G.char ['a'..'z']                               
    alphas = G.fix1 $ \p ->
      (:) <$> alpha <*> p <|> pure []

-- similar, but alls are defined via gfixn 
example6 :: Grammar ExChar ()
example6 = finalize $ unCPS $ do
  (_ :< _ :< tree :< forest :< _) <- G.fixn $
    (Rec $ \_ -> foldr1 (<|>) $ map G.char ['a'..'z'])
    :<
    (Rec $ \(alpha :< alphas :< _) ->
        (:) <$> alpha <*> alphas <|> pure [])
    :<
    (Rec $ \(_ :< alphas :< _ :< forest :< _) ->
        () <$ alphas <* G.spaces <* G.text "[" <* forest <* G.text "]")
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

        
