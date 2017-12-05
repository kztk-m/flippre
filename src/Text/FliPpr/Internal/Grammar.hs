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
import Text.FliPpr.Doc as D 
import Data.Kind

import Text.FliPpr.Internal.Type as T
import Data.Typeable ((:~:)(Refl), Proxy(..))

import Prelude hiding ((.), id)
import Control.Category ((.), id) 
import Control.Applicative (Alternative(..)) 

import Control.Monad.Reader
import Control.Monad.State 

type EnvRep = U 

type V  = Var  EnvRep
type VT = VarT EnvRep 
type E  = Env  EnvRep
type E' t env = Env' EnvRep t env 

data None (env :: [Type]) a = None

data Grammar a =
  forall env. Grammar (V env a) (E' RHS env) 

data GrammarA info a =
  forall env. GrammarA (V env a) (E' RHS env) (E' info env) 

newtype RHS (env :: [Type])  a = RHS { getRHS :: [ Prod env a ] }

data Symb env a where
  TermC  :: Char -> Symb env Char 
  TermP  :: (Char -> Bool) -> Symb env Char
  NT     :: V env a -> Symb env a
  Space  :: Symb env ()
  Spaces :: Symb env ()

data Prod (env :: [Type]) a where
  PNil    :: a -> Prod env a
  PCons   :: Symb env a -> Prod env (a -> b) -> Prod env b

instance Shiftable EnvRep Prod where
  shift = shiftProd

instance Shiftable EnvRep RHS where
  shift vt (RHS ps) = RHS (map (shift vt) ps)

shiftProd :: VT env env' -> Prod env a -> Prod env' a
shiftProd vt (PNil a)    = PNil a
shiftProd vt (PCons s r) = PCons (shift vt s) (shiftProd vt r) 

instance Shiftable EnvRep Symb where
  shift vt (TermC c) = TermC c
  shift vt (TermP p) = TermP p
  shift vt (NT v)    = NT (runVarT vt v) 
  shift vt Space     = Space
  shift vt Spaces    = Spaces 

-- UC: Under Construction
newtype GrammarUC a =
  GB { runGB :: forall env. E' RHSUC env -> GR env a }

data GR env a =
  forall env'. GR (RHSUC env' a) (E' RHSUC env') (VT env env') 

data RHSUC env a = RUnion  (RHSUC env a) (RHSUC env a)
                 | REmpty
                 | RSingle (ProdUC env a) 
                 | RUnInit

instance Shiftable EnvRep RHSUC where
  shift vt (RUnion r1 r2) = RUnion (shift vt r1) (shift vt r2)
  shift vt REmpty         = REmpty
  shift vt (RSingle p)    = RSingle (shift vt p)
  shift vt RUnInit        = RUnInit 

finalizeRHS :: RHSUC env a -> RHS env a
finalizeRHS x = RHS (go x [])
  where
    go (RUnion x y) r = go x (go y r)
    go (RSingle p)  r = finalizeProd p : r
    go _            r = r

finalizeProd :: ProdUC env a -> Prod env a 
finalizeProd x = fnaive id x -- go id x PNil 
  where
    -- naive :: ProdUC env a -> Prod env a
    -- naive (PPure f)   = PNil f
    -- naive (PSymb s)   = PCons s (PNil id)
    -- naive (PMult p q) = naiveF id p (naive q)  

    -- fnaive = fmap f . naive 
    fnaive ::(a -> b) -> ProdUC env a -> Prod env b
    fnaive f (PPure a)   = PNil (f a)
    fnaive f (PSymb s)   = PCons s (PNil f)
    fnaive f (PMult p q) = go (f.) p (\g -> fnaive g q)
--      fmap f (fmap id (naive p) `prod` (naive q))
      
    -- fmapProd :: (a -> b) -> Prod env a -> Prod env b
    -- fmapProd = undefined 

    -- -- naiveF f p q = fmap f (naive p) <*> q 
    -- naiveF :: (x -> (a -> b)) -> ProdUC env x -> Prod env a -> Prod env b
    -- naiveF f (PPure a)   r = fmapProd (f a) r
    -- naiveF f (PSymb s)   r = PCons s $ fmapProd (\a c -> f c a) r
    -- naiveF f (PMult p q) r =
    --   naiveF (flip ($) . (f.)) p (naiveF (\a b f -> f a b) q r)

    -- go f p (r g) = naiveF f p (fmap g (r id))

    go :: (x -> (a -> b)) -> ProdUC env x -> (forall r. (a -> r) -> Prod env r) -> Prod env b
    go f (PPure a) r = r (f a)
    go f (PSymb s) r = PCons s $ r (\a c -> f c a)
    go f (PMult p q) r =
      go (flip ($) . (f.)) p (\k -> go (\a b -> k (\f -> f a b)) q r)
{-

prod :: Prod env (a -> b) -> Prod env a -> Prod env b 

naive :: ProdUC env a -> Prod a
naive (PPure f)   = PNil f
naive (PSymb s)   = PCons s (PNil id)
naive (PMult p q) = go p `prod` go q

define naiveR x q = prod (naive x) q


naiveR (PPure f)   r = PNil f `prod` r
naiveR (PSymb s)   r = PCons s (PNil id) `prod` r
navieR (PMult p q) r = (naive p `prod` naive q) `prod` r  
                     = (fmap ... (naive p)) `prod` (fmap ... (naive q) <*> naive r)

define naiveF f x q = fmap f (naive x) `prod` q 

naiveF :: (x -> (a -> b)) -> ProdUC x -> Prod a -> Prod b

naiveF f (PPure a) r = fmap f (PNil a) <*> r
 = PNil (f a) <*> r
 = fmap (f a) r 
naiveF f (PSymb s) r = fmap f (PCons s (PNil id)) <*> r
 = PCons s (PNil f) <*> r
 = PCons s (fmap (\k a -> k (f a)) r)
naiveF f (PMult p q) r 
 = fmap f (naive p <*> naive q) <*> r
 = (fmap (f.) naive p <*> naive q) <*> r
 = fmap (f.) (fmap (flip ($))) (naive p) <*>
   (fmap (\a b f -> f a b) (naive q) <*> r)
 = naiveF ((f.) . flip ($)) p (naiveF (\a b f -> f a b) q r)


(p <*> q) <*> r
= fmap (\f k -> k f) p <*> (fmap (\a b f -> f a b) q <*> r)


go :: ProdUC env (a -> b) -> Prod a -> Prod b 
go (PPure f)   r = PNil f `prod` r
go (PSymb s)   r = PCons s (PNil id) `prod` r
go (PMult p q) r = go p (go q r) 

go :: ProdUC env (a -> b) -> Prod a -> Prod b 
go (PPure f)   r = fmap f r
go (PSymb s)   r = PCons f (PNil id) `prod` r
go (PMult p q) r = go p (go q r) 



-}

{-


pure f <*> symb a
=> PCons a $ PNil f 

pure f <*> symb a <*> symb
=> PCons a $ PCons b $ PNil (\b a -> f a b)

pure f ; k
=> _ (k f) 

symb a ; k 
=> PCons a $ _ (\c -> k c)

p <*> q ; k
=> (p ; ?) (q ; _) 

(pure f <*> symb a)
=> PCons a $ _ (\c -> f c)

-}

--       go :: (t -> (a -> b)) -> Prod env t -> Prod env a -> Prod env b
--       go k (PNil f) p = fmap (k f) p
--       go k (PCons c r) p = PCons c (go (\g a cv -> k (g cv) a) r p)

                
data ProdUC env a where
  PSymb :: Symb env a -> ProdUC env a
  PMult :: ProdUC env (a -> b) -> ProdUC env a -> ProdUC env b
  PPure :: a -> ProdUC env a 

instance Shiftable EnvRep ProdUC where
  shift vt (PSymb a)   = PSymb (shift vt a)
  shift vt (PMult p q) = PMult (shift vt p) (shift vt q)
  shift vt (PPure a)   = PPure a 

instance Functor (ProdUC env) where
  fmap f (PSymb s) = PPure f `PMult` PSymb s
  fmap f (PPure a)    = PPure (f a)
  fmap f (PMult a r)  = PMult (fmap (f.) a) r

instance Applicative (ProdUC env) where
  pure = PPure
  (<*>) = PMult

instance Functor (RHSUC env) where
  fmap f (RUnion a b) = RUnion (fmap f a) (fmap f b)
  fmap f (REmpty)     = REmpty
  fmap f (RSingle p)  = RSingle (fmap f p) 
  fmap f RUnInit      = RUnInit 

instance  Applicative (RHSUC env) where
  pure a = RSingle (pure a)

  (RUnion f g) <*> a = RUnion (f <*> a) (g <*> a)
  REmpty <*> _       = REmpty
  RSingle f <*> RUnion a b = RUnion (RSingle f <*> a) (RSingle f <*> b)
  RSingle f <*> REmpty     = REmpty
  RSingle f <*> RSingle a  = RSingle (f <*> a)
  _ <*> _                  = error "Shouldn't happen."  
  

-- instance Functor (Prod env) where
--   fmap f (PNil k)    = PNil (f k)
--   fmap f (PCons a r) = PCons a (fmap (f .) r) 

-- instance Applicative (Prod env) where
--   pure a = PNil a
--   p1 <*> p2 = go id p1 p2 
--     where
--       go :: (t -> (a -> b)) -> Prod env t -> Prod env a -> Prod env b
--       go k (PNil f) p = fmap (k f) p
--       go k (PCons c r) p = PCons c (go (\g a cv -> k (g cv) a) r p)


-- instance Functor (RHS env) where
--   fmap f (RHS ps) = RHS (fmap (fmap f) ps)

-- instance Applicative (RHS env) where
--   pure f = RHS [pure f]
--   RHS ps1 <*> RHS ps2 = RHS [ p1 <*> p2 | p1 <- ps1, p2 <- ps2 ]

-- instance Alternative (RHS env) where
--   empty = RHS []
--   RHS ps1 <|> RHS ps2 = RHS (ps1 ++ ps2) 
                           
instance Functor GrammarUC where
  fmap f x = pure f <*> x 

atmostSingle :: RHSUC env a -> Bool
atmostSingle = (>0) . go 2
  where
    go lim _ | lim <= 0  = 0
    go lim REmpty        = lim
    go lim RUnInit       = 0
    go lim (RSingle _  ) = lim - 1
    go lim (RUnion x y)  = go (go lim x) y 

instance Applicative GrammarUC where
  -- pure a = GB $ \env -> let (env1, r1, vt) = E.extendEnv env (Unions [ PNil a ])
  --                       in GR r1 (E.mapEnv (shift vt) env1) vt 

  pure a = GB $ \env -> GR (RSingle (pure a)) env id 

  GB k1 <*> GB k2 = GB $ \env ->
    case k1 env of
      GR ps1 env1 vt1 ->
        case k2 env1 of
          GR ps2 env2 vt2 ->
            if atmostSingle ps1 && atmostSingle ps2 then
              GR (shift vt2 ps1 <*> ps2) env2 (vt2 . vt1)
            else
              let (env3, r3, vt3) = E.extendEnv' env2 (shift vt2 ps1)
                  (env4, r4, vt4) = E.extendEnv' env3 (shift vt3 ps2)
              in GR (RSingle (makeMultS (NT (shift vt4 r3)) (NT r4))) env4 (vt4 . vt3 . vt2 . vt1)
    where
      makeMultS :: Symb env (a -> b) -> Symb env a -> ProdUC env b
      makeMultS s1 s2 = (PSymb s1) <*> (PSymb s2)
  
  -- GB k1 <*> GB k2 = GB $ \env ->
  --   case k1 env of
  --     GR r1 env1 vt1 ->
  --       case k2 env1 of
  --         GR r2 env2 vt2 ->
  --           let Unions ps = E.lookupEnv (runVarT vt2 r1) env2
  --               (env3', r3, vt3) =
  --                 E.extendEnv env2 (Unions [ PCons (NT (runVarT vt2 r1)) $
  --                                            PCons (NT r2) $
  --                                            PNil  (flip ($)) ])
  --               env3 = E.mapEnv (shift vt3) env3'
  --           in GR r3 env3 (vt3 . vt2 . vt1)
  
instance Alternative GrammarUC where
  -- empty = GB $ \env ->
  --                let (env1, r1, vt) = E.extendEnv env (RHS [])
  --                in GR r1 (E.mapEnv (shift vt) env1) vt
  empty = GB $ \env -> GR (REmpty) env id 

  GB k1 <|> GB k2 = GB $ \env ->
    case k1 env of
      GR ps1 env1 vt1 ->
        case k2 env1 of
          GR ps2 env2 vt2 ->
            GR (RUnion ps2 (shift vt2 ps1)) env2 (vt2 . vt1) 
  
  -- GB k1 <|> GB k2 = GB $ \env ->
  --   case k1 env of
  --     GR r1 env1 vt1 ->
  --       case k2 env1 of
  --         GR r2 env2 vt2 ->
  --           let RHS ps1 = E.lookupEnv (runVarT vt2 r1) env2
  --               env3 = E.modifyEnv r2 (\(RHS ps2) -> RHS (ps2 ++ ps1)) env2
  --           in GR r2 env3 (vt2 . vt1)

gempty :: GrammarUC a
gempty = Control.Applicative.empty 

liftProdLiteral :: (forall env. ProdUC env a) -> GrammarUC a
liftProdLiteral p = GB $ \env -> GR (RSingle p) env id

liftSymbLiteral :: (forall env. Symb env a) -> GrammarUC a
liftSymbLiteral s = liftProdLiteral (PSymb s)

gchar :: Char -> GrammarUC Char
gchar c = liftSymbLiteral (TermC c)
                  -- let (env1, r1, vt) = E.extendEnv env (Unions [ PCons (TermC c) $ PNil id ] )
                  -- in GR r1 (E.mapEnv (shift vt) env1) vt 

gsatisfy :: (Char -> Bool) -> GrammarUC Char
gsatisfy p = liftSymbLiteral (TermP p) 
                  -- let (env1, r1, vt) = E.extendEnv env (Unions [ PCons (TermP p) $ PNil id ] )
                  -- in GR r1 (E.mapEnv (shift vt) env1) vt

gtext :: String -> GrammarUC String
gtext s = liftProdLiteral (fromText s)
                  -- let (env1, r1, vt) = E.extendEnv env (Unions [ fromText s ])
                  -- in GR r1 (E.mapEnv (shift vt) env1) vt
  where
    fromText :: String -> ProdUC env String
    fromText = go 
      where
        go ""     = pure ""
        go (c:cs) = (:) <$> PSymb (TermC c) <*> go cs
        -- go :: (String -> r) -> String -> Prod env r
        -- go k ""     = PNil  (k "")
        -- go k (c:cs) = PCons (TermC c) (go (\s c -> k (c:s)) cs)

gfix :: (GrammarUC a -> GrammarUC a) -> GrammarUC a
gfix f = gfixn (to . f . from) from
  where
    from :: Apps GrammarUC '[a] -> GrammarUC a 
    from (a :> End) = a
    to a = a :> End 
-- gfix f = GB $ \env ->
--   let (env1, r1, vt) = E.extendEnv' env (RUnInit)
--       res = f (GB $ \env' -> GR (RSingle $ PSymb (NT (E.embedVar (repOf env1) (repOf env') r1))) env' id)
--   in case runGB res env1 of
--        GR ps2 env2 vt2 ->
--          let r1'   = shift vt2 r1
--              env2' = E.updateEnv r1' ps2 env2
--          in GR (RSingle $ PSymb (NT r1')) env2' (vt2 . vt)


-- -- still not ok 
-- gbfix2 :: ((GrammarUC a, GrammarUC b) -> (GrammarUC a, GrammarUC b)) ->
--           ((GrammarUC a, GrammarUC b) -> GrammarUC r) ->
--           GrammarUC r
-- gbfix2 f k = GB $ \env ->
--   let (env1, r1, vt1)   = E.extendEnv' env (RUnInit)
--       (env2, r2, vt2)   = E.extendEnv' env1 (RUnInit)
--       makeNT r env env' = PSymb (NT (E.embedVar (repOf env) (repOf env') r)) 
--       captureR r oenv (GB k) = GB $ \env1' ->
--         case k env1' of
--           GR ps1' env1' vt1' -> GR (RSingle $ makeNT r oenv env1')
--                                 (E.updateEnv (E.embedVar (repOf oenv) (repOf env1') r) ps1' env1') vt1'
--       g1 = GB $ \env -> GR (RSingle $ makeNT r1 env1 env) env id
--       g2 = GB $ \env -> GR (RSingle $ makeNT r2 env2 env) env id 
--       k' (x,y) = k (captureR r1 env1 x, captureR r2 env2 y)
--   in case runGB (k' (f (g1, g2))) env2 of
--        GR psR envR vtR -> GR psR envR (vtR . vt2 . vt1) 
       
newtype GBT   a = GBT { runGBT :: GrammarUC a -> GrammarUC a }
data TravR env ts = forall env'. TravR (E' RHSUC env') (Apps GBT ts) (Apps GrammarUC ts) (VT env env')

data MkG a = MkG { runMkG :: forall env. E' RHSUC env -> MkGR env a }
data MkGR env a = forall env'. MkGR (E' RHSUC env') a (VT env env')
data ((f :: k -> Type) :*: (g :: k -> Type)) a = f a :*: g a

instance Functor MkG where
  fmap f (MkG k) = MkG $ \e -> case k e of
    MkGR env' a vt -> MkGR env' (f a) vt

instance Applicative MkG where
  pure a = MkG $ \e -> MkGR e a id
  MkG k1 <*> MkG k2 = MkG $ \e ->
    case k1 e of
      MkGR e1 a1 vt1 ->
        case k2 e1 of
          MkGR e2 a2 vt2 -> MkGR e2 (a1 a2) (vt2 . vt1)

prepareGlue :: f a -> MkG ((GBT :*: GrammarUC) a)
prepareGlue _ = MkG $ \e ->
  let (env1, r1, vt1) = E.extendEnv' e RUnInit 
      capture (GB k) = GB $ \e ->
              case E.lookupEnv (convV r1 env1 e) e of
                RUnInit -> 
                  case k e of
                    GR ps ev vt -> GR (RSingle $ makeNT r1 env1 ev)
                                   (E.updateEnv (convV r1 env1 ev) ps ev) vt
                _ ->
                  GR (RSingle (PSymb (NT (convV r1 env1 e)))) e id
      entry = GB $ \e -> GR (RSingle $ makeNT r1 env1 e) e id
  in MkGR env1 (GBT capture :*: entry) vt1
  where
    makeNT r env env' = PSymb (NT (E.embedVar (repOf env) (repOf env') r)) 
    convV  r env env' = E.embedVar (repOf env) (repOf env') r 
    

gfixn :: forall ts r.
          TypeList ts =>
          (Apps GrammarUC ts -> Apps GrammarUC ts) ->
          (Apps GrammarUC ts -> GrammarUC r) -> GrammarUC r
gfixn f k = GB $ \env -> case runMkG glue env of
  MkGR envI ciI vtI ->
    let captureI = mapApps (\(f :*: _) -> f) ciI
        initI    = mapApps (\(_ :*: g) -> g) ciI
        capture xs = zipWithApps (\(GBT f) -> f) captureI xs
    in case runGB (k (iterate (capture . f) initI !! nts)) envI of
         GR psR envR vtR ->
           GR psR envR (vtR . vtI)
  where    
    nts   = appsLength (Proxy :: Proxy ts) 
    shape = appsShape  (Proxy :: Proxy ts)

    glue = traverseApps prepareGlue shape


newtype GBTp p a =
  GBTp { runGBTp :: (GrammarUC :.: p) a -> (GrammarUC :.: p) a }

prepareGlueP :: f a -> MkG ((GBTp p  :*: (GrammarUC :.: p)) a)
prepareGlueP _ = MkG $ \e ->
  let (env1, r1, vt1) = E.extendEnv' e RUnInit 
      capture (GB k) = GB $ \e ->
              case E.lookupEnv (convV r1 env1 e) e of
                RUnInit -> 
                  case k e of
                    GR ps ev vt -> GR (RSingle $ makeNT r1 env1 ev)
                                   (E.updateEnv (convV r1 env1 ev) ps ev) vt
                _ ->
                  GR (RSingle (PSymb (NT (convV r1 env1 e)))) e id
      entry = GB $ \e -> GR (RSingle $ makeNT r1 env1 e) e id
  in MkGR env1 (GBTp (Comp . capture . getComp) :*: Comp entry) vt1
  where
    makeNT r env env' = PSymb (NT (E.embedVar (repOf env) (repOf env') r)) 
    convV  r env env' = E.embedVar (repOf env) (repOf env') r 


gfixnp :: forall ts p r.
          TypeList (ts :: [k]) =>
          (Apps (GrammarUC :.: p) ts -> Apps (GrammarUC :.: p) ts) ->
          (Apps (GrammarUC :.: p) ts -> (GrammarUC :.: p) r) -> (GrammarUC :.: p) r
gfixnp f k = Comp $ GB $ \env -> case runMkG glue env of
  MkGR envI ciI vtI ->
    let captureI = mapApps (\(f :*: _) -> f) ciI
        initI    = mapApps (\(_ :*: g) -> g) ciI
        capture xs = zipWithApps (\(GBTp f) -> f) captureI xs
    in case runGB (getComp $ k (iterate (capture . f) initI !! nts)) envI of
         GR psR envR vtR ->
           GR psR envR (vtR . vtI)
  where    
    nts   = appsLength (Proxy :: Proxy ts) 
    shape = appsShape  (Proxy :: Proxy ts)

    glue = traverseApps prepareGlueP shape

gspace :: GrammarUC ()
gspace = liftSymbLiteral Space

gspaces :: GrammarUC ()
gspaces = liftSymbLiteral Spaces 

finalize :: GrammarUC a -> Grammar a
finalize (GB k) =
  case k E.emptyEnv of
    GR ps env vt ->
      let (env1, r1, vt1) = E.extendEnv' env ps
      in Grammar r1 (mapEnv finalizeRHS env1)

toGrammar :: Tr m RHSUC RHSUC a -> m '[] -> Grammar a
toGrammar (Tr k) m0 =
  case k m0 E.emptyEnv of
    TrR ps _ env _ ->
      let (env1, r1, _) = E.extendEnv' env (unFree ps)
      in Grammar r1 (mapEnv finalizeRHS env1) 

{-
Reduce a grammar, with a simple inlining 
-}



data RedMap env new =
  RedMap { runRedMap :: forall a. V env a -> Maybe (V new a) }

newtype Tr m rhs res a =
  Tr { runTr :: forall old.
                m old -> E' rhs old -> TrR m rhs res old a }

data TrR m rhs res old a =
  forall new. TrR (FreeA res new a) (m new) (E' rhs new)  (VT old new)


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
  shift vt (FPure a)   = FPure a
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

type TrG m a = Tr m RHSUC RHSUC a 
  
prodOpt :: (forall env env'. VT env env' -> m env -> m env') ->
           TrG m (a -> b) -> TrG m a -> TrG m b 
prodOpt shifter (Tr f) (Tr a) = Tr $ \m env ->
  case f m env of
    TrR res1 m1 env1 vt1 ->
      case a m1 env1 of
        TrR res2 m2 env2 vt2 ->
          case refine (shift vt2 res1) env2 of
            GR res1' env3 vt3 ->
              case refine (shift vt3 res2) env3 of
                GR res2' env4 vt4 ->
                  TrR (FRaw (shift vt4 res1' <*> res2'))
                      (shifter (vt4 . vt3) m2)
                      env4
                      (vt4 . vt3 . vt2 . vt1)
  where
    refine :: FreeA RHSUC env a -> E' RHSUC env -> GR env a
    refine (unFree -> ps) env
      | atmostSingle ps = GR ps env id
      | otherwise       = let (env', r', vt') = E.extendEnv' env ps
                          in  GR (RSingle (PSymb (NT r'))) env' vt' 

-- data RedR new a = forall upd. RedR (RHSUC upd a) (E' RHSUC upd) (VT new upd)

makeAlt :: TrG m a -> TrG m a -> TrG m a
makeAlt (Tr a) (Tr b) = Tr $ \m env ->
  case a m env of
    TrR res1 m1 env1 vt1 ->
      case b m1 env1 of
        TrR res2 m2 env2 vt2 -> 
          TrR (FRaw $ unFree (shift vt2 res1) `RUnion` unFree res2) m2 env2 (vt2 . vt1)

reduce :: Grammar a -> Grammar a
reduce (Grammar v oldEnv) =
  toGrammar (work (E.lookupEnv v oldEnv) oldEnv) (RedMap $ const Nothing) 
  where
    -- TODO: The current implementation is a bit too conservative
    -- in inlining. It would generate a grammar with the rules of the form
    -- of Pk = Pj.

    work :: RHS env a -> E' RHS env -> Tr (RedMap env) RHSUC RHSUC a
    work (RHS [])     oldRules = Tr $ \m e -> TrR (FRaw REmpty) m e id
    work (RHS [s])    oldRules = workProd s oldRules 
    work (RHS (s:ss)) oldRules =
      makeAlt (workProd s oldRules) (work (RHS ss) oldRules) 

    workProd :: Prod env a -> E' RHS env -> Tr (RedMap env) RHSUC RHSUC a
    workProd (PNil a) oldRules = pure a
    workProd (PCons a f) oldRules =
      makeProd (fmap (\a k -> k a) (workSymb a oldRules)) (workProd f oldRules)

    makeProd = prodOpt shifter
      where
        shifter vt m = RedMap $ fmap (shift vt) . runRedMap m 

    workSymb :: Symb env a -> E' RHS env -> Tr (RedMap env) RHSUC RHSUC a
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

    workSymb (TermC c) oldRules =
      Tr $ \m e -> TrR (FRaw $ RSingle (PSymb (TermC c))) m e id 
    workSymb (TermP c) oldRules =
      Tr $ \m e -> TrR (FRaw $ RSingle (PSymb (TermP c))) m e id 
    workSymb (Space) oldRules =
      Tr $ \m e -> TrR (FRaw $ RSingle (PSymb (Space))) m e id 
    workSymb (Spaces) oldRules =
      Tr $ \m e -> TrR (FRaw $ RSingle (PSymb (Spaces))) m e id 

    inlinable :: RHS env a -> Bool
    inlinable (RHS [])  = True
    inlinable (RHS [s]) = isConstant s
    inlinable _         = False

    isConstant :: Prod env a -> Bool
    isConstant (PNil _) = True
    isConstant (PCons s r) =
      nonNT s && isConstant r
      where
        nonNT (NT _) = False
        nonNT _      = True 
          


instance Pretty (Symb env a) where
  ppr (TermC c) = text (show c)
  ppr (TermP _) = text "<abstract>"
  ppr (NT    x) = text ("P" ++ showVar x)
  ppr (Space)   = text "_"
  ppr (Spaces)  = text "<spaces>"

instance Pretty (Prod env a) where
  ppr (PNil _) = text (show "")
  ppr p        = ppr' p 
    where      
      pprRest :: Doc -> Prod env b -> Doc 
      pprRest d (PNil _) = d 
      pprRest d r        = d D.<+> ppr' r 

      ppr' :: Prod env c -> Doc
      ppr' = go ""
        where
          go :: String -> Prod env c -> Doc 
          go s (PNil _)            = pprS s D.empty
          go s (PCons (TermC c) r) = go (c:s) r
          go s (PCons t r)         = pprS s $ pprRest (ppr t) r

          pprS "" d = d
          pprS s  d = D.text (show $ reverse s) D.<+> d 
      

instance Pretty (RHS env a) where
  ppr (RHS []) = text "<empty>"
  ppr (RHS ss) = group $ arrange (map (align . ppr) ss)
    where
      arrange :: [Doc] -> Doc
      arrange [d1, d2]     = group (go [d1,d2]) 
      arrange [d1, d2, d3] = group (go [d1,d2,d3]) 
      arrange (d1 : d2 : d3 : d4 : r) = group (go [d1,d2,d3,d4]) </> D.text "|" <+> arrange r
      arrange x = go x

      go :: [Doc] -> Doc
      go []     = D.empty
      go [d]    = d
      go (d:ds) = d </> text "|" <+> go ds 
      -- arrange [d] = d
      -- arrange [d1,d2] = group (d1 </> text "|" <+> d2)
      -- arrange [d1,d2,d3,d4] = group (
  
  -- ppr (RHS [])     = text "<empty>"
  -- ppr (RHS (s:ss)) = align (group (go s ss))
  --   where
  --     go s []      = ppr s
  --     go s (s':ss) = align (ppr s) </> D.text "|" <+> go s' ss 
    
instance Pretty (Grammar a) where
  ppr (Grammar r env) =
    D.text "start:" <+> D.text ("P" ++ E.showVar r) <>
    nest 2 (linebreak <> E.pprEnv (const ppr) (D.text "P") env)

instance Show (Grammar a) where
  show = show . ppr 

example1 :: Grammar ()
example1 = finalize $ gfix $ \p ->
  () <$ gtext "(" <* p <* gtext ")" <* p
  <|> pure () 
  
                               
example2 :: Grammar ()
example2 = finalize $
  let f (a,b) =
        (() <$ alphas <* gspaces <* gtext "[" <* b <* gtext "]",
         () <$ a <* gspaces <* gtext "," <* gspaces <* b 
         <|> () <$ a
         <|> pure ())
  in gfix $ \x -> fst (f (x, gfix $ \y -> snd (f (x,y))))
  where
    alpha = gfix $ \p ->
      foldr1 (<|>) $ map gchar ['a'..'z']                               
    alphas = gfix $ \p ->
      (:) <$> alpha <*> p <|> pure []

{-
Implementing mutual recursions by Bekic's lemma causes grammar-size blow-up.
-} 
example3 :: Grammar ()
example3 = finalize $
  let f (a,b) =
        (() <$ alphas <* gspaces <* gtext "[" <* b <* gtext "]",
         () <$ a <* gspaces <* gtext "," <* gspaces <* b 
         <|> () <$ a
         <|> pure ())
      p1 = gfix $ \x -> fst (f (x, gfix $ \y -> snd (f (x,y))))
      p2 = gfix $ \y -> snd (f (gfix $ \x -> fst (f (x,y)), y))
  in p1 <|> p2 
  where
    alpha = gfix $ \p ->
      foldr1 (<|>) $ map gchar ['a'..'z']                               
    alphas = gfix $ \p ->
      (:) <$> alpha <*> p <|> pure []

-- sample4 :: Grammar ()
-- sample4 = finalize $
--   let f (a,b) =
--         (() <$ alphas <* gspaces <* gtext "[" <* b <* gtext "]",
--          () <$ a <* gspaces <* gtext "," <* gspaces <* b 
--          <|> () <$ a
--          <|> pure ())
--   in gfix2 f (\(p1,p2) -> p1 <|> p2)
--   where
--     alpha = gfix $ \p ->
--       foldr1 (<|>) $ map gchar ['a'..'z']                               
--     alphas = gfix $ \p ->
--       (:) <$> alpha <*> p <|> pure []

example5 :: Grammar ()
example5 = finalize $
  let f (a,b) =
        (() <$ alphas <* gspaces <* gtext "[" <* b <* gtext "]",
         () <$ a <* gspaces <* gtext "," <* gspaces <* b 
         <|> () <$ a
         <|> pure ())
  in gfixn
      ((\(a :> b :> End) -> let (a',b') = f (a,b)
                            in a' :> b' :> End)
       :: Apps GrammarUC [(), ()] -> Apps GrammarUC [(), ()])
      (\(p1 :> p2 :> End) -> p1 <|> p2)
  where
    alpha = gfix $ \p ->
      foldr1 (<|>) $ map gchar ['a'..'z']                               
    alphas = gfix $ \p ->
      (:) <$> alpha <*> p <|> pure []

-- similar, but alls are defined via gfixn 
example6 :: Grammar ()
example6 = finalize $
  gfixn ((\(alpha :> alphas :> tree :> forest :> End) ->
             (foldr1 (<|>) $ map gchar ['a'..'z']) :>
             ( (:) <$> alpha <*> alphas <|> pure [] ) :>
             ( () <$ alphas <* gspaces <* gtext "[" <* forest <* gtext "]") :>
             ( () <$ tree <* gspaces <* gtext "," <* gspaces <* forest
               <|> () <$ tree <|> pure () ) :> End)
          :: Apps GrammarUC [Char, String, (), ()]
             -> Apps GrammarUC [Char, String, (), ()])
         (\(_ :> _ :> tree :> forest :> End) -> tree <|> forest)

        
