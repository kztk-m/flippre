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

module Text.FliPpr.Internal.Grammar where

import Text.FliPpr.Internal.Env as E
import Text.FliPpr.Doc as D 
import Data.Kind

import Text.FliPpr.Internal.Type (TypeList(..))

import Prelude hiding ((.), id)
import Control.Category ((.), id) 
import Control.Applicative (Alternative(..)) 

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


newtype GrammarBuffer a =
  GB { runGB :: forall env. E' RHS env -> GR env a }

data GR env a =
  forall env'. GR (RHS env' a) (E' RHS env') (VT env env') 


instance Functor (Prod env) where
  fmap f (PNil k)    = PNil (f k)
  fmap f (PCons a r) = PCons a (fmap (f .) r) 

instance Applicative (Prod env) where
  pure a = PNil a
  p1 <*> p2 = go id p1 p2 
    where
      go :: (t -> (a -> b)) -> Prod env t -> Prod env a -> Prod env b
      go k (PNil f) p = fmap (k f) p
      go k (PCons c r) p = PCons c (go (\g a cv -> k (g cv) a) r p)


instance Functor (RHS env) where
  fmap f (RHS ps) = RHS (fmap (fmap f) ps)

instance Applicative (RHS env) where
  pure f = RHS [pure f]
  RHS ps1 <*> RHS ps2 = RHS [ p1 <*> p2 | p1 <- ps1, p2 <- ps2 ]

instance Alternative (RHS env) where
  empty = RHS []
  RHS ps1 <|> RHS ps2 = RHS (ps1 ++ ps2) 
                           
instance Functor GrammarBuffer where
  fmap f x = pure f <*> x 

instance Applicative GrammarBuffer where
  -- pure a = GB $ \env -> let (env1, r1, vt) = E.extendEnv env (Unions [ PNil a ])
  --                       in GR r1 (E.mapEnv (shift vt) env1) vt 

  pure a = GB $ \env -> GR (RHS [PNil a]) env id 

  GB k1 <*> GB k2 = GB $ \env ->
    case k1 env of
      GR ps1 env1 vt1 ->
        case k2 env1 of
          GR ps2 env2 vt2 ->
            if length (getRHS ps1) <= 1 && length (getRHS ps2) <= 1 then
              GR (shift vt2 ps1 <*> ps2) env2 (vt2 . vt1)
            else
              let (env3, r3, vt3) = E.extendEnv' env2 (shift vt2 ps1)
                  (env4, r4, vt4) = E.extendEnv' env3 (shift vt3 ps2)
              in GR (RHS [ makeMultS (NT (shift vt4 r3)) (NT r4) ]) env4 (vt4 . vt3 . vt2 . vt1)
    where
      makeMultS :: Symb env (a -> b) -> Symb env a -> Prod env b
      makeMultS s1 s2 = PCons s1 $ PCons s2 $ PNil (flip ($))
  
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
  
instance Alternative GrammarBuffer where
  -- empty = GB $ \env ->
  --                let (env1, r1, vt) = E.extendEnv env (RHS [])
  --                in GR r1 (E.mapEnv (shift vt) env1) vt
  empty = GB $ \env -> GR (RHS []) env id 

  GB k1 <|> GB k2 = GB $ \env ->
    case k1 env of
      GR (RHS ps1) env1 vt1 ->
        case k2 env1 of
          GR (RHS ps2) env2 vt2 ->
            GR (RHS (ps2 ++ map (shift vt2) ps1)) env2 (vt2 . vt1) 
  
  -- GB k1 <|> GB k2 = GB $ \env ->
  --   case k1 env of
  --     GR r1 env1 vt1 ->
  --       case k2 env1 of
  --         GR r2 env2 vt2 ->
  --           let RHS ps1 = E.lookupEnv (runVarT vt2 r1) env2
  --               env3 = E.modifyEnv r2 (\(RHS ps2) -> RHS (ps2 ++ ps1)) env2
  --           in GR r2 env3 (vt2 . vt1)

liftProdLiteral :: (forall env. Prod env a) -> GrammarBuffer a
liftProdLiteral p = GB $ \env -> GR (RHS [p]) env id

liftSymbLiteral :: (forall env. Symb env a) -> GrammarBuffer a
liftSymbLiteral s = liftProdLiteral (PCons s (PNil id))

gbchar :: Char -> GrammarBuffer Char
gbchar c = liftSymbLiteral (TermC c)
                  -- let (env1, r1, vt) = E.extendEnv env (Unions [ PCons (TermC c) $ PNil id ] )
                  -- in GR r1 (E.mapEnv (shift vt) env1) vt 

gbsatisfy :: (Char -> Bool) -> GrammarBuffer Char
gbsatisfy p = liftSymbLiteral (TermP p) 
                  -- let (env1, r1, vt) = E.extendEnv env (Unions [ PCons (TermP p) $ PNil id ] )
                  -- in GR r1 (E.mapEnv (shift vt) env1) vt

gbtext :: String -> GrammarBuffer String
gbtext s = liftProdLiteral (fromText s)
                  -- let (env1, r1, vt) = E.extendEnv env (Unions [ fromText s ])
                  -- in GR r1 (E.mapEnv (shift vt) env1) vt
  where
    fromText :: String -> Prod env String
    fromText = go id
      where
        go :: (String -> r) -> String -> Prod env r
        go k ""     = PNil  (k "")
        go k (c:cs) = PCons (TermC c) (go (\s c -> k (c:s)) cs)

gbfix :: (GrammarBuffer a -> GrammarBuffer a) -> GrammarBuffer a
gbfix f = GB $ \env ->
  let (env1, r1, vt) = E.extendEnv' env (RHS [])
      res = f (GB $ \env' -> GR (RHS [PCons (NT (E.embedVar (repOf env1) (repOf env') r1)) (PNil id)]) env' id)
  in case runGB res env1 of
       GR ps2 env2 vt2 ->
         let r1'   = shift vt2 r1
             env2' = E.updateEnv r1' ps2 env2
         in GR (RHS [PCons (NT r1') (PNil id)]) env2' (vt2 . vt)


gbspace :: GrammarBuffer ()
gbspace = liftSymbLiteral Space

gbspaces :: GrammarBuffer ()
gbspaces = liftSymbLiteral Spaces 

finalize :: GrammarBuffer a -> Grammar a
finalize (GB k) =
  case k E.emptyEnv of
    GR ps env vt ->
      let (env1, r1, vt1) = E.extendEnv' env ps
      in Grammar r1 env1 


instance Pretty (Symb env a) where
  ppr (TermC c) = text (show c)
  ppr (TermP _) = text "<abstract>"
  ppr (NT    x) = text ("P" ++ showVar x)
  ppr (Space)   = text "_"
  ppr (Spaces)  = text "<spaces>"

instance Pretty (Prod env a) where
  ppr (PNil _)    = text (show "")
  ppr (PCons p r) = go (ppr p) r 
    where      
      go :: Doc -> Prod env b -> Doc 
      go d (PNil _)    = d 
      go d (PCons s r) = d <+> go (ppr s) r 

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

sample1 :: Grammar ()
sample1 = finalize $ gbfix $ \p ->
  () <$ gbtext "(" <* p <* gbtext ")" <* p
  <|> pure () 
  
                               
sample2 :: Grammar ()
sample2 = finalize $
  let f (a,b) =
        (() <$ alphas <* gbspaces <* gbtext "[" <* b <* gbtext "]",
         () <$ a <* gbspaces <* gbtext "," <* gbspaces <* b 
         <|> () <$ a
         <|> pure ())
  in gbfix $ \x -> fst (f (x, gbfix $ \y -> snd (f (x,y))))
  where
    alpha = gbfix $ \p ->
      foldr1 (<|>) $ map gbchar ['a'..'z']                               
    alphas = gbfix $ \p ->
      (:) <$> alpha <*> p <|> pure []

{-
Implementing mutual recursions by Bekic's lemma causes grammar-size blow-up.
-} 
sample3 :: Grammar ()
sample3 = finalize $
  let f (a,b) =
        (() <$ alphas <* gbspaces <* gbtext "[" <* b <* gbtext "]",
         () <$ a <* gbspaces <* gbtext "," <* gbspaces <* b 
         <|> () <$ a
         <|> pure ())
      p1 = gbfix $ \x -> fst (f (x, gbfix $ \y -> snd (f (x,y))))
      p2 = gbfix $ \y -> snd (f (gbfix $ \x -> fst (f (x,y)), y))
  in p1 <|> p2 
  where
    alpha = gbfix $ \p ->
      foldr1 (<|>) $ map gbchar ['a'..'z']                               
    alphas = gbfix $ \p ->
      (:) <$> alpha <*> p <|> pure []

        
