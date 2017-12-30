{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}

module Text.FliPpr.Internal.Grammar.Type where

import Data.Kind
import Data.Functor.Identity 

import Control.Category
import Prelude hiding (id, (.))
import Control.Applicative (Alternative(..))
import Data.Typeable ((:~:)(..))

import Text.FliPpr.Internal.Env as E
import Text.FliPpr.Doc as D
import Text.FliPpr.Container2
import Text.FliPpr.Internal.CPS
import Text.FliPpr.Internal.Type as T (Rec(..), adjustRec2)

type EnvRep = U 

type V  = Var  EnvRep
type VT = VarT EnvRep 
type E  = Env  EnvRep
type E' t env = Env' EnvRep t env 


{- |
Definition of a grammar type obtained from

Baars et al.: Typed Transformations of Typed Grammars: The Left Corner
Transform, ENTCS 253 (2010) 51-64.
-}
data Grammar c a =
  forall env. Grammar (V env a) (E' (RHS c) env) 

data RHS c (env :: [Type])  a = RHS { getRHS :: [ Prod c env a ], isVoid :: Maybe (a :~: ()) }

data Symb c env a where
  TermC  :: c -> Symb c env c
  TermP  :: (c -> Bool) -> Symb c env c 
  NT     :: V env a -> Symb c env a

data Prod c (env :: [Type]) a where
  PNil    :: a -> Prod c env a
  PCons   :: Symb c env a -> Prod c env (a -> b) -> Prod c env b

instance Shiftable EnvRep (Prod c) where
  shift _  (PNil a)    = PNil a
  shift vt (PCons s r) = PCons (shift vt s) (shift vt r) 

instance Shiftable EnvRep (RHS c) where
  shift vt (RHS ps b) = RHS (map (shift vt) ps) b

instance Shiftable EnvRep (Symb c) where
  shift _  (TermC c) = TermC c
  shift _  (TermP p) = TermP p
  shift vt (NT v)    = NT (runVarT vt v) 


instance Pretty c => Pretty (Symb c env a) where
  ppr (TermC c) = D.ppr c
  ppr (TermP _) = D.text "<abstract>"
  ppr (NT    x) = D.text ("P" ++ showVar x)

instance Pretty c => Pretty (Prod c env a) where
  ppr (PNil _) = D.text (show "")
  ppr p        = ppr' p 
    where      
      pprRest :: Pretty c => Doc -> Prod c env b -> Doc 
      pprRest d (PNil _) = d 
      pprRest d r        = d D.<+> ppr' r 

      ppr' :: Pretty c => Prod c env a' -> Doc
      ppr' = go []
        where
          go :: Pretty c => [c] -> Prod c env a' -> Doc 
          go s (PNil _)            = pprS s D.empty
          go s (PCons (TermC c) r) = go (c:s) r
          go s (PCons t r)         = pprS s $ pprRest (ppr t) r

          pprS [] d = d
          pprS s  d = D.ppr (reverse s) D.<+> d 
      

instance Pretty c => Pretty (RHS c env a) where
  ppr (RHS xs b) = case b of
    Just _  -> D.text "{" D.<> pprRHS xs D.<> D.text "}"
    Nothing -> pprRHS xs 
    where
      pprRHS [] = D.text "<empty>"
      pprRHS ss = group $ arrange (map (align . ppr) ss) 
      
      arrange :: [Doc] -> Doc
      arrange [d1, d2]     = group (go [d1,d2]) 
      arrange [d1, d2, d3] = group (go [d1,d2,d3]) 
      arrange (d1 : d2 : d3 : d4 : r) = group (go [d1,d2,d3,d4]) </> D.text "|" <+> arrange r
      arrange x = go x

      go :: [Doc] -> Doc
      go []     = D.empty
      go [d]    = d
      go (d:ds) = d </> D.text "|" <+> go ds 
    
instance Pretty c => Pretty (Grammar c a) where
  ppr (Grammar r env) =
    D.text "start:" <+> D.text ("P" ++ E.showVar r) <>
    nest 2 (linebreak <> E.pprEnv (const ppr) (D.text "P") env)

instance Pretty c => Show (Grammar c a) where
  show = show . ppr 


{- |
A grammar being constructed via 'Applicative" interface.

OpenGrammar a =
 ∀env. E' OpenRHS env -> ∃env'. (OpenRHS env' a, E' OpenRHS env', VT env env')

-}
newtype OpenGrammar c a =
  OpenG { runOpenG :: forall env. E' (OpenRHS c) env -> ResultG c env a }

data ResultG c env a =
  forall env'. ResultG (OpenRHS c env' a) (E' (OpenRHS c) env') (VT env env') 

data OpenRHS c env a where
  RUnion  :: OpenRHS c env a -> OpenRHS c env a -> OpenRHS c env a 
  REmpty  :: OpenRHS c env a 
  RSingle :: OpenProd c env a -> OpenRHS c env a 
  RUnInit :: OpenRHS c env a
  RVoid   :: OpenRHS c env () -> OpenRHS c env () 

rvoid :: OpenRHS c env () -> OpenRHS c env ()
rvoid (RVoid r) = RVoid r
rvoid r         = RVoid r 

runion :: OpenRHS c env a -> OpenRHS c env a -> OpenRHS c env a
runion REmpty r = r
runion r REmpty = r
runion (RVoid r1) r2 = rvoid (runion r1 r2)
runion r1 (RVoid r2) = rvoid (runion r1 r2) 
runion r1 r2    = RUnion r1 r2 

instance Shiftable EnvRep (OpenRHS c) where
  shift vt (RUnion r1 r2) = RUnion (shift vt r1) (shift vt r2)
  shift _  REmpty         = REmpty
  shift vt (RSingle p)    = RSingle (shift vt p)
  shift _  RUnInit        = RUnInit 
  shift vt (RVoid r)      = RVoid (shift vt r) 

data OpenProd c env a where
  PSymb :: Symb c env a -> OpenProd c env a
  PMult :: OpenProd c env (a -> b) -> OpenProd c env a -> OpenProd c env b
  PPure :: a -> OpenProd c env a 

instance Shiftable EnvRep (OpenProd c) where
  shift vt (PSymb a)   = PSymb (shift vt a)
  shift vt (PMult p q) = PMult (shift vt p) (shift vt q)
  shift _  (PPure a)   = PPure a

instance Functor (OpenProd c env) where
  fmap f (PSymb s) = PPure f `PMult` PSymb s
  fmap f (PPure a)    = PPure (f a)
  fmap f (PMult a r)  = PMult (fmap (f.) a) r

instance Applicative (OpenProd c env) where
  pure = PPure
  (<*>) = PMult


finalize :: OpenGrammar c a -> Grammar c a
finalize (OpenG k) =
  case k E.emptyEnv of
    ResultG ps env _ ->
      case ps of
        RSingle (PSymb (NT n)) ->
          Grammar n (mapEnv finalizeRHS env)
        _ ->       
          let (env1, r1, _) = E.extendEnv' env ps
          in Grammar r1 (mapEnv finalizeRHS env1)

finalizeRHS :: OpenRHS c env a -> RHS c env a
finalizeRHS x = go x (RHS [] Nothing) 
  where
    go :: OpenRHS c env a -> RHS c env a -> RHS c env a 
    go (RUnion x y) r = go x (go y r)
    go (RSingle p)  r = RHS (finalizeProd p : getRHS r) Nothing
    go (RVoid p)    r = goVoid p (RHS (getRHS r) (Just Refl))
    go _            r = r

    goVoid :: OpenRHS c env a -> RHS c env () -> RHS c env ()
    goVoid (RUnion x y) r = goVoid x (goVoid y r)
    goVoid (RSingle p)  r = RHS (finalizeProdV p : getRHS r) (isVoid r)
    goVoid (RVoid p)    r = goVoid p r
    goVoid _            r = r

finalizeProdV :: OpenProd c env a -> Prod c env ()
finalizeProdV = fnaive ()
  where
    fnaive :: b -> OpenProd c env a -> Prod c env b
    fnaive f (PPure _)   = PNil f
    fnaive f (PSymb s)   = PCons s (PNil (const f))
    fnaive f (PMult p q) = go f p (\g -> fnaive g q)

    go :: b -> OpenProd c env x -> (forall r. r -> Prod c env r) -> Prod c env b
    go f (PPure _) r   = r f
    go f (PSymb s) r   = PCons s $ r (const f)
    go f (PMult p q) r = go f p (\k -> go k q r)                           
    

finalizeProd :: OpenProd c env a -> Prod c env a 
finalizeProd = fnaive id 
  where
    -- naive :: ProdUC env a -> Prod env a
    -- naive (PPure f)   = PNil f
    -- naive (PSymb s)   = PCons s (PNil id)
    -- naive (PMult p q) = naiveF id p (naive q)  

    -- fnaive = fmap f . naive 
    fnaive :: (a -> b) -> OpenProd c env a -> Prod c env b
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

    go :: (x -> (a -> b)) -> OpenProd c env x -> (forall r. (a -> r) -> Prod c env r) -> Prod c env b
    go f (PPure a) r = r (f a)
    go f (PSymb s) r = PCons s $ r (flip f)
    go f (PMult p q) r =
      go (flip ($) . (f.)) p (\k -> go (\a b -> k (\f -> f a b)) q r)

                

instance Functor (OpenRHS c env) where
  fmap f (RUnion a b) = RUnion (fmap f a) (fmap f b)
  fmap _ REmpty       = REmpty
  fmap f (RSingle p)  = RSingle (fmap f p) 
  fmap _ RUnInit      = RUnInit 
  fmap f (RVoid p)    = fmap (f . const ()) p 

instance  Applicative (OpenRHS c env) where
  pure a = RSingle (pure a)

  (RUnion f g) <*> a = runion (f <*> a) (g <*> a)
  REmpty <*> _       = REmpty
  RSingle f <*> RUnion a b = runion (RSingle f <*> a) (RSingle f <*> b)
  RSingle _ <*> REmpty     = REmpty
  RSingle f <*> RSingle a  = RSingle (f <*> a)
  RSingle f <*> RVoid p    = RSingle (fmap (. const ()) f) <*> p
  _ <*> _                  = error "Shouldn't happen."  
  
atmostSingle :: OpenRHS c env a -> Bool
atmostSingle = (>0) . go 2
  where
    go :: Int -> OpenRHS c env a -> Int 
    go lim  _ | lim <= 0  = 0
    go lim  REmpty        = lim
    go _    RUnInit       = error "Shouldn't happen." 
    go lim  (RSingle _  ) = lim - 1
    go lim  (RUnion x y)  = go (go lim x) y
    go lim  (RVoid p)     = go lim p 

                             
instance Functor (OpenGrammar c) where
  fmap f (OpenG k) = OpenG $ \env ->
    case k env of
      ResultG r1 env1 vt1 -> ResultG (fmap f r1) env1 vt1 
    

shareRHS :: OpenRHS c env a -> E' (OpenRHS c) env -> ResultG c env a
shareRHS r env
  | atmostSingle r = ResultG r env id
  | otherwise      =
    let (env1, v1, vt1) = E.extendEnv' env r 
    in ResultG (RSingle (PSymb (NT v1))) env1 vt1 

instance Applicative (OpenGrammar c) where
  pure a = OpenG $ \env -> ResultG (RSingle (pure a)) env id 

  OpenG k1 <*> OpenG k2 = OpenG $ \env ->
    case k1 env of
      ResultG r1 env1 vt1 ->
        case k2 env1 of
          ResultG r2 env2 vt2 ->
            if (atmostSingle r1 || atmostSingle r2) then
              ResultG (shift vt2 r1 <*> r2) env2 (vt2 . vt1) 
            else             
              case shareRHS (shift vt2 r1) env2 of
                ResultG r3 env3 vt3 ->
                  case shareRHS (shift vt3 r2) env3 of
                    ResultG r4 env4 vt4 ->
                      ResultG (shift vt4 r3 <*> r4) env4 (vt4 . vt3 . vt2 . vt1)

  x <* y = fmap const x <*> discard y
  x *> y = fmap (flip const) (discard x) <*> y 
  

instance Alternative (OpenGrammar c) where
  empty = OpenG $ \env -> ResultG REmpty env id 

  OpenG k1 <|> OpenG k2 = OpenG $ \env ->
    case k1 env of
      ResultG ps1 env1 vt1 ->
        case k2 env1 of
          ResultG ps2 env2 vt2 ->
            ResultG (runion ps2 (shift vt2 ps1)) env2 (vt2 . vt1) 
                

liftProdLiteral :: (forall env. OpenProd c env a) -> OpenGrammar c a
liftProdLiteral p = OpenG $ \env -> ResultG (RSingle p) env id

liftSymbLiteral :: (forall env. Symb c env a) -> OpenGrammar c a
liftSymbLiteral s = liftProdLiteral (PSymb s)

class CharLike c where
  fromChar :: Char -> c 
  liftPred :: (Char -> Bool) -> c -> Bool 

term :: c -> OpenGrammar c c
term c = liftSymbLiteral (TermC c)

char :: CharLike c => Char -> OpenGrammar c c
char c = liftSymbLiteral (TermC (fromChar c))

satisfy :: CharLike c => (Char -> Bool) -> OpenGrammar c c
satisfy p = liftSymbLiteral (TermP (liftPred p))

text :: CharLike c => String -> OpenGrammar c [c]
text s = liftProdLiteral (fromText s)
  where
    fromText :: CharLike c => String -> OpenProd c env [c]
    fromText []     = pure []
    fromText (c:cs) = (:) <$> PSymb (TermC $ fromChar c) <*> fromText cs


data ExChar = NormalChar Char | Space | Spaces 

instance CharLike ExChar where
  fromChar = NormalChar
  liftPred p (NormalChar c) = p c
  liftPred _ _              = False 

instance Pretty ExChar where
  ppr (NormalChar c) = ppr c
  ppr Space          = D.text "_"
  ppr Spaces         = D.text "<spaces>"

  pprList = uncurry pprList' . chars []
    where
      chars s (NormalChar c:cs) = chars (c:s) cs
      chars s r                 = (reverse s, r)

      pprList' [] []     = D.text ""      
      pprList' [] (c:cs) = ppr c D.<+> pprList cs
      pprList' s  [] = D.ppr s
      pprList' s  r  = D.ppr s D.<+> pprList r 


                               


discard :: OpenGrammar c a -> OpenGrammar c ()
discard (OpenG k) = OpenG $ \env ->
  case k env of
    ResultG rhs env vt -> ResultG (rvoid $ fmap (const ()) rhs) env vt
 

space :: OpenGrammar ExChar ()
space = discard $ liftSymbLiteral (TermC Space)

spaces :: OpenGrammar ExChar ()
spaces = discard $ liftSymbLiteral (TermC Spaces)



newtype MkG c a = MkG { runMkG :: forall env. E' (OpenRHS c) env -> ResultMkG c env a }
data ResultMkG c env a = forall env'. ResultMkG (E' (OpenRHS c) env') a (VT env env')

data ((f :: k -> Type) :*: (g :: k -> Type)) a = f a :*: g a
newtype ((f :: k' -> Type) :.: (g :: k -> k')) a = Comp { getComp :: f (g a) }

infixl 5 :.:


instance Functor (MkG c) where
  fmap f (MkG k) = MkG $ \e -> case k e of
    ResultMkG env' a vt -> ResultMkG env' (f a) vt

instance Applicative (MkG c) where
  pure a = MkG $ \e -> ResultMkG e a id
  MkG k1 <*> MkG k2 = MkG $ \e ->
    case k1 e of
      ResultMkG e1 a1 vt1 ->
        case k2 e1 of
          ResultMkG e2 a2 vt2 -> ResultMkG e2 (a1 a2) (vt2 . vt1)


newtype GTp c p a =
  GTp { runGTp :: (OpenGrammar c :.: p) a -> (OpenGrammar c :.: p) a }

prepareGlueP :: f a -> MkG c ((GTp c p  :*: (OpenGrammar c :.: p)) a)
prepareGlueP _ = MkG $ \e ->
  let (env1, r1, vt1) = E.extendEnv' e RUnInit 
      capture (OpenG k) = OpenG $ \e ->
              case E.lookupEnv (convV r1 env1 e) e of
                RUnInit -> 
                  case k e of
                    ResultG ps ev vt -> ResultG (RSingle $ makeNT r1 env1 ev)
                                        (E.updateEnv (convV r1 env1 ev) ps ev) vt
                _ ->
                  ResultG (RSingle (PSymb (NT (convV r1 env1 e)))) e id
      entry = OpenG $ \e -> ResultG (RSingle $ makeNT r1 env1 e) e id
  in ResultMkG env1 (GTp (Comp . capture . getComp) :*: Comp entry) vt1
  where
    makeNT r env env' = PSymb (NT (E.embedVar (repOf env) (repOf env') r)) 
    convV  r env env' = E.embedVar (repOf env) (repOf env') r 

fixGen ::
  Container2 k =>
  k (Rec k (OpenGrammar c :.: p)) -> CPS (OpenGrammar c :.: p) (k (OpenGrammar c :.: p))
fixGen defs = cps $ \k -> Comp $ OpenG $ \env -> case runMkG glue env of
  ResultMkG envI ciI vtI ->
    let captureI = fmap2 (\(f :*: _) -> f) ciI
        initI    = fmap2 (\(_ :*: g) -> g) ciI
        capture  = zipWith2 (\(GTp f) -> f) captureI 
    in case runOpenG (getComp $ k (comp nts initI capture defs)) envI of
      ResultG psR envR vtR ->
        ResultG psR envR (vtR . vtI) 
  where
    comp 0 is _  _ = is
    comp n is st f =
      let x = comp (n-1) is st f
      in st (fmap2 (\r -> runRec r x) f)
    
    nts  = length2   defs 
    glue = traverse2 prepareGlueP defs


fixn ::
  Container2 k =>
  k (Rec k (OpenGrammar c)) -> CPS (OpenGrammar c) (k (OpenGrammar c))
fixn defs = fmap (fmap2 elimI) $ 
  adjustCont2 elimI introI $
    fixGen (fmap2 (T.adjustRec2 introI elimI) defs)

  where
    introI :: OpenGrammar c a -> (OpenGrammar c :.: Identity) a
    introI g = Comp $ fmap return g

    elimI :: (OpenGrammar c :.: Identity) a -> OpenGrammar c a
    elimI (Comp g) = fmap runIdentity g 


fix1 :: (OpenGrammar c a -> OpenGrammar c a) -> OpenGrammar c a
fix1 f = runCPS (fixn (Single $ Rec $ f . from)) from
  where
    from :: Single a (OpenGrammar c) -> OpenGrammar c a 
    from (Single a) = a
       

share :: OpenGrammar c a -> CPS (OpenGrammar c) (OpenGrammar c a)
share (OpenG def) = cps $ \k -> OpenG $ \env ->
  case def env of
    ResultG ps1 env1 vt1 ->
      let (env2, r2, vt2) = E.extendEnv' env1 ps1
      in case runOpenG (k (OpenG $ \env' ->
                                  ResultG (RSingle $ ntWithLift env2 env' r2)
                         env' id)) env2 of
           ResultG psN envN vtN ->
             ResultG psN envN (vtN . vt2 . vt1)
  where
    ntWithLift :: E' (OpenRHS c) env -> E' (OpenRHS c) env' -> V env a -> OpenProd c env' a
    ntWithLift e e' r = PSymb $ NT $ E.embedVar (repOf e) (repOf e') r
