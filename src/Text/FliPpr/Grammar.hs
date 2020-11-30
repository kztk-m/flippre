{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Text.FliPpr.Grammar
  ( Grammar (..),
    GrammarD,
    ExChar (..),
    CharLike (..),
    char,
    symbols,
    text,
    space,
    spaces,
    simplifyGrammar,
    withSpace,
    pprGrammar,
    pprAsFlat,
    module Defs,
  )
where

import Control.Applicative (Alternative (..))
import Control.Category (Category (..), id, (.))
import Control.Monad (forM)
import Control.Monad.State (MonadState, State, StateT (..), evalState, get, put)
import Data.Foldable (asum)
import qualified Data.Map as Map
import Data.RangeSet.List (RSet)
import qualified Data.RangeSet.List as RS
import Data.Typeable ((:~:) (..))
--
import Debug.Trace (trace)
import qualified Text.FliPpr.Doc as D
import Text.FliPpr.Internal.Defs as Defs
import qualified Text.FliPpr.Internal.Env as E
import Prelude hiding (id, (.))

class (Applicative e, Alternative e) => Grammar c e | e -> c where
  symb :: c -> e c
  symbI :: RSet c -> e c

  -- | Same as @fmap . const@ but this would be useful for further optimization.
  --   TODO: Remove it, as it is not used.
  constantResult :: a -> e t -> e a
  constantResult f e = f <$ e

symbols :: Grammar c e => [c] -> e [c]
symbols = foldr (\a r -> (:) <$> symb a <*> r) (pure [])

type GrammarD c e = (Defs e, Grammar c e)

newtype NonterminalPrinterM c a = NonterminalPrinterM {runNonterminalPrinterM :: State Int a}
  deriving (Functor, Applicative, Monad, MonadState Int)

instance Defs.VarM (NonterminalPrinterM c) where
  newVar = do
    i <- get
    put $! i + 1
    return $ "N" ++ show i

  nestScope = id

instance Functor (PprDefs (NonterminalPrinterM c)) where
  fmap _ (PprDefs h) = PprDefs h

instance Applicative (PprDefs (NonterminalPrinterM c)) where
  pure _ = PprDefs $ \_ -> return $ D.text "ε"
  f <*> a = PprDefs $ \k -> (\d1 d2 -> D.parensIf (k > 9) $ d1 D.<+> D.align d2) <$> pprDefs f 9 <*> pprDefs a 10

instance Alternative (PprDefs (NonterminalPrinterM c)) where
  empty = PprDefs $ \_ -> return $ D.text "⊥"
  f <|> g = PprDefs $ \k -> (\d1 d2 -> D.parensIf (k > 3) $ D.sep [d1, D.text "|", d2]) <$> pprDefs f 3 <*> pprDefs g 3

  many = Defs.manyD
  some = Defs.someD

instance Show c => Grammar c (PprDefs (NonterminalPrinterM c)) where
  symb c = PprDefs $ \_ -> return $ D.text (show c)
  symbI cs = PprDefs $ \_ -> return $ D.text (show cs)

pprGrammar :: Show c => PprDefs (NonterminalPrinterM c) _a -> D.Doc
pprGrammar g =
  evalState (runNonterminalPrinterM (pprDefs g 0)) 1

data ExChar
  = Space
  | Spaces
  | NormalChar Char
  deriving (Eq, Ord)

instance Enum ExChar where
  toEnum 0 = Space
  toEnum 1 = Spaces
  toEnum n = NormalChar (toEnum (n -2))

  fromEnum Space = 0
  fromEnum Spaces = 1
  fromEnum (NormalChar c) = fromEnum c + 2

  succ Space = Spaces
  succ Spaces = NormalChar minBound
  succ (NormalChar c) = NormalChar (succ c)

  pred Spaces = Space
  pred (NormalChar c)
    | c == minBound = Spaces
    | otherwise = NormalChar (pred c)
  pred Space = error "pred: no predecessor"

instance D.Pretty ExChar where
  ppr (NormalChar c) = D.ppr c
  ppr Space = D.text "_"
  ppr Spaces = D.text "<spaces>"

  pprList = uncurry pprList' . chars []
    where
      chars s (NormalChar c : cs) = chars (c : s) cs
      chars s r = (reverse s, r)

      pprList' [] [] = D.text ""
      pprList' [] (c : cs) = case cs of [] -> D.ppr c; _ -> D.ppr c D.<+> D.pprList cs
      pprList' s [] = D.ppr s
      pprList' s r = D.ppr s D.<+> D.pprList r

instance Show ExChar where
  show = show . D.ppr
  showList s = \r -> show (D.pprList s) ++ r

class CharLike c where
  fromChar :: Char -> c

instance CharLike Char where
  fromChar = id

instance CharLike ExChar where
  fromChar = NormalChar

char :: (CharLike c, Grammar c e) => Char -> e c
char c = symb (fromChar c)

text :: (CharLike c, Grammar c e) => String -> e [c]
text = foldr (\c r -> (:) <$> char c <*> r) (pure [])

space :: Grammar ExChar e => e ()
space = constantResult () $ symb Space

spaces :: Grammar ExChar e => e ()
spaces = constantResult () $ symb Spaces

type Env = E.Env E.U

type Var = E.Var E.U

-- data VEnv f env where
--   VNil :: VEnv f '[]
--   VCons :: f a -> VEnv f as -> VEnv f (a ': as)

-- vmap :: (forall a. f a -> g a) -> VEnv f env -> VEnv g env
-- vmap _ VNil = VNil
-- vmap f (VCons a as) = VCons (f a) (vmap f as)

-- lookupVEnv :: Var env a -> VEnv f env -> f a
-- lookupVEnv VZ (VCons a _) = a
-- lookupVEnv (VS x) (VCons _ r) = lookupVEnv x r

-- updateVEnv :: Var env a -> f a -> VEnv f env -> VEnv f env
-- updateVEnv VZ v (VCons _ r) = VCons v r
-- updateVEnv (VS x) v (VCons a r) = VCons a (updateVEnv x v r)

-- type RepEnv env = VEnv Proxy env

-- toRep :: VEnv f env -> RepEnv env
-- toRep = vmap h
--   where
--     h :: f a -> Proxy a
--     h _ = Proxy

-- --- Assumption: env' contains env
-- diffRep :: RepEnv env -> RepEnv env' -> VarT env env'
-- diffRep xs ys = go (len ys - len xs) xs ys
--   where
--     len :: RepEnv env -> Int
--     len VNil = 0
--     len (VCons _ r) = 1 + len r

--     go :: Int -> RepEnv env -> RepEnv env' -> VarT env env'
--     go 0 _ _ = unsafeCoerce $ VarT id
--     go n r1 (VCons _ r2) = vstep . go (n -1) r1 r2
--     go _ _ _ = error "diffRep: invariant violation."

type Bindings c env1 env2 = Env (RHS c env1) env2

newtype RHS c env a = RHS [Prod c env a]
  deriving (Functor)

instance Show c => D.Pretty (RHS c env a) where
  ppr (RHS rs) =
    D.punctuate (D.line D.<> D.text "|" D.<> D.text " ") $ map D.ppr rs

data FlatGrammar c a = forall env. FlatGrammar (Bindings c env env) (RHS c env a)

pprAsFlat :: Show c => ToFlatGrammar c a -> D.Doc
pprAsFlat = D.ppr . flatten

instance Show c => D.Pretty (FlatGrammar c a) where
  ppr (FlatGrammar bs r) =
    D.align (E.pprEnv pprDef bs D.</> pprDefN (D.text "Start") r)
    where
      pprDef x rhs = D.text ("N" ++ x) D.<+> D.group (D.align (D.text "=" D.<+> D.ppr rhs))
      pprDefN n rhs = D.hsep [n, D.text "=", D.align (D.ppr rhs)]

data Prod c env a = PNil a | forall b. PCons (Symb c env b) (Prod c env (b -> a))

instance Show c => D.Pretty (Prod c env a) where
  ppr (PNil _) = D.text "ε"
  ppr (PCons s r) = go (D.ppr s) r
    where
      go :: forall a. D.Doc -> Prod c env a -> D.Doc
      go d (PNil _) = d
      go d (PCons ss rr) = d D.<+> go (D.ppr ss) rr

instance Functor (Prod c env) where
  fmap f (PNil a) = PNil (f a)
  fmap f (PCons s r) = PCons s (fmap (f .) r)

-- data Var env a where
--   VZ :: Var (a : env) a
--   VS :: Var env a -> Var (b : env) a

-- eqVar :: Var env a -> Var env b -> Maybe (a :~: b)
-- eqVar VZ VZ = Just Refl
-- eqVar VZ _ = Nothing
-- eqVar (VS _) VZ = Nothing
-- eqVar (VS x) (VS y) = eqVar x y

data Symb c env a where
  NT :: !(Var env a) -> Symb c env a
  Symb :: !c -> Symb c env c
  SymbI :: !(RSet c) -> Symb c env c

instance Show c => D.Pretty (Symb c env a) where
  ppr (NT x) = D.text ("N" ++ E.showVar x)
  ppr (Symb c) = D.text (show c)
  ppr (SymbI cs) = D.text (show cs)

-- newtype VarT env env' = VarT {runVarT :: forall a. Var env a -> Var env' a}

-- vstep :: VarT env (a : env)
-- vstep = VarT VS

-- instance Category VarT where
--   id = VarT id
--   VarT f . VarT g = VarT (f . g)

-- class Shiftable k where
--   shift :: VarT env env' -> k env a -> k env' a

-- instance Shiftable Var where
--   shift = runVarT

instance E.Shiftable E.U (Symb c) where
  shift diff (NT x) = NT (E.shift diff x)
  shift _ (Symb c) = Symb c
  shift _ (SymbI cs) = SymbI cs

instance E.Shiftable E.U (Prod c) where
  shift _ (PNil a) = PNil a
  shift diff (PCons s r) = PCons (E.shift diff s) $ E.shift diff r

instance E.Shiftable E.U (RHS c) where
  shift diff (RHS rs) = RHS $ map (E.shift diff) rs

type Diff env env' = E.VarT E.U env env'

data Res c env a = forall env'. Res (Bindings c env' env') (RHS c env' a) (Diff env env')

instance Functor (Res c env) where
  fmap f (Res bs rhs diff) = Res bs (fmap f rhs) diff

-- FIXME: This implementation is inefficient due to repeated shifting.
-- So, we need to abstract environments for faster manipulatoin and
-- avoid re-traversal of data-structures by delaying shifting.

newtype ToFlatGrammar c a = ToFlatGrammar {toFlatGrammar :: forall env. Bindings c env env -> Res c env a}
  deriving (Functor)

instance Applicative (Prod c env) where
  pure = PNil
  (<*>) = go id
    where
      -- Derived from the following definition.
      -- PNil a <*> f = fmap a f
      -- PCons a as <*> r = PCons a (flip <$> as <*> r)
      go :: (a -> b -> r) -> Prod c env a -> Prod c env b -> Prod c env r
      go f (PNil a) r = fmap (f a) r
      go f (PCons a as) r = PCons a (go (flip . (f .)) as r)

instance Applicative (ToFlatGrammar c) where
  pure a = ToFlatGrammar $ \defs -> Res defs (RHS [PNil a]) id
  f <*> x = ToFlatGrammar $ \defs ->
    case toFlatGrammar f defs of
      Res defs1 rhs1 diff1 ->
        case toFlatGrammar x defs1 of
          Res defs2 rhs2 diff2 ->
            case (rhs1, rhs2) of
              (RHS [], _) -> Res defs2 (RHS []) (diff2 . diff1)
              (_, RHS []) -> Res defs2 (RHS []) (diff2 . diff1)
              (RHS [a], RHS [b]) -> Res defs2 (RHS [E.shift diff2 a <*> b]) (diff2 . diff1)
              _ ->
                let (defs3, x, diff3) = E.extendEnv defs2 (E.shift diff2 rhs1)
                    (defs4, y, diff4) = E.extendEnv (E.mapEnv (E.shift diff3) defs3) (E.shift diff3 rhs2)
                 in Res (E.mapEnv (E.shift diff4) defs4) (RHS [PCons (NT $ E.shift diff4 x) (PNil id) <*> PCons (NT y) (PNil id)]) (diff4 . diff3 . diff2 . diff1)

-- let defs3 = VCons (shift (vstep . diff2) rhs1) (vmap (shift vstep) defs2)
--     defs4 = VCons (shift (vstep . vstep) rhs2) (vmap (shift vstep) defs3)
--  in Res defs4 (RHS [PCons (NT (VS VZ)) (PNil id) <*> PCons (NT VZ) (PNil id)]) (vstep . vstep . diff2 . diff1)

instance Alternative (ToFlatGrammar c) where
  empty = ToFlatGrammar $ \defs -> Res defs (RHS []) id
  a1 <|> a2 = ToFlatGrammar $ \defs ->
    case toFlatGrammar a1 defs of
      Res defs1 (RHS ps1) diff1 ->
        case toFlatGrammar a2 defs1 of
          Res defs2 (RHS ps2) diff2 ->
            Res defs2 (RHS (map (E.shift diff2) ps1 ++ ps2)) (diff2 . diff1)

  many = Defs.manyD
  some = Defs.someD

instance Grammar c (ToFlatGrammar c) where
  symb c = ToFlatGrammar $ \defs -> Res defs (RHS [PCons (Symb c) $ PNil id]) id
  symbI cs = ToFlatGrammar $ \defs -> Res defs (RHS [PCons (SymbI cs) $ PNil id]) id

  constantResult = (<$)

type Value = Defs.DTypeVal

valueMap :: (forall a. f a -> g a) -> Value f a -> Value g a
valueMap f (VT a) = VT (f a)
valueMap f (VProd x y) = VProd (valueMap f x) (valueMap f y)

data Ress c env a = forall env'. Ress (Bindings c env' env') (Value (RHS c env') a) (Diff env env')

instance Defs (ToFlatGrammar c) where
  newtype Rules (ToFlatGrammar c) a = ToFlatGrammars {toFlatGrammars :: forall env. Bindings c env env -> Ress c env a}

  lift c = ToFlatGrammars $ \defs ->
    case toFlatGrammar c defs of
      Res defs' r' diff' -> Ress defs' (VT r') diff'

  unlift c = ToFlatGrammar $ \defs ->
    case toFlatGrammars c defs of
      Ress defs' (VT r') diff' -> Res defs' r' diff'

  pairRules x y = ToFlatGrammars $ \defs -> case toFlatGrammars x defs of
    Ress defs1 r1 diff1 -> case toFlatGrammars y defs1 of
      Ress defs2 r2 diff2 -> Ress defs2 (VProd (valueMap (E.shift diff2) r1) r2) (diff2 . diff1)

  unpairRules xy k = ToFlatGrammars $ \defs ->
    case toFlatGrammars xy defs of
      Ress defs1 (VProd a b) diff1 ->
        let argA = ToFlatGrammars $ \defs' -> let diff' = E.diffRep (E.repOf defs1) (E.repOf defs') in Ress defs' (valueMap (E.shift diff') a) id
            argB = ToFlatGrammars $ \defs' -> let diff' = E.diffRep (E.repOf defs1) (E.repOf defs') in Ress defs' (valueMap (E.shift diff') b) id
         in case toFlatGrammars (k argA argB) defs1 of
              Ress defs2 r diff2 -> Ress defs2 r (diff2 . diff1)

  letr h = ToFlatGrammars $ \defs ->
    let (defs1, x, diff) = E.extendEnv defs (RHS []) -- a placeholder
        argH = ToFlatGrammar $ \defs' -> let diff' = E.diffRep (E.repOf defs1) (E.repOf defs') in Res defs' (E.shift diff' $ RHS [PCons (NT x) $ PNil id]) id
     in case toFlatGrammars (h argH) $ E.mapEnv (E.shift diff) defs1 of
          Ress defs2 (VProd (VT r) res) diff2 ->
            let defs2' = E.updateEnv (E.shift diff2 x) r defs2
             in Ress defs2' res (diff2 . diff)

flatten :: ToFlatGrammar c a -> FlatGrammar c a
flatten g =
  case toFlatGrammar g E.emptyEnv of
    Res defs r _ -> FlatGrammar defs r

-- a simple optimizing interpretation
-- We use the property that
--
--   symb a <|> symb b = symbI (RS.singleton a `RS.union` RS.singleton b)
--
-- Also we perform simple inlining: For h :: (a -> a * r) -> r, if e1 of
--    <e1, e2> = h (Complex a)
-- is still simple, we can replace it with (snd . h) e1

data Opt c g a where
  OptSymb :: c -> Opt c g c
  OptSymbI :: RSet c -> Opt c g c
  OptEmpty :: Opt c g a
  OptPure :: a -> Opt c g a
  OptSimple :: g a -> Opt c g a -- inlinable
  OptOther :: g a -> Opt c g a

simplifyGrammar :: Grammar c g => Opt c g a -> g a
simplifyGrammar = unOpt

unOpt :: Grammar c g => Opt c g a -> g a
unOpt (OptSymb c) = symb c
unOpt (OptSymbI cs) = symbI cs
unOpt OptEmpty = empty
unOpt (OptPure a) = pure a
unOpt (OptSimple p) = p
unOpt (OptOther p) = p

isSimpleEnough :: Opt c g a -> Bool
isSimpleEnough (OptOther _) = False
isSimpleEnough _ = True

instance Grammar c g => Functor (Opt c g) where
  fmap f (OptPure a) = OptPure (f a)
  fmap _ OptEmpty = OptEmpty
  fmap f p
    | isSimpleEnough p = OptSimple $ fmap f (unOpt p)
    | otherwise = OptOther $ fmap f (unOpt p)

instance Grammar c g => Applicative (Opt c g) where
  pure a = OptPure a

  --  _ <*> _ | trace "<*>" False = undefined
  OptEmpty <*> _ = OptEmpty
  _ <*> OptEmpty = OptEmpty
  OptPure f <*> g = fmap f g
  f <*> OptPure g = fmap ($ g) f
  f <*> g = OptOther $ unOpt f <*> unOpt g

instance (Defs g, Ord c, Enum c, Grammar c g) => Alternative (Opt c g) where
  empty = OptEmpty

  --  _ <|> _ | trace "<|>" False = undefined
  OptEmpty <|> e = e
  OptSymb a <|> OptSymb b = OptSymbI (RS.fromList [a, b])
  OptSymb a <|> OptSymbI bs = OptSymbI (RS.insert a bs)
  OptSymbI as <|> OptSymb b = OptSymbI (RS.insert b as)
  OptSymbI as <|> OptSymbI bs = OptSymbI (RS.union as bs)
  e <|> OptEmpty = e
  g1 <|> g2 = OptOther (unOpt g1 <|> unOpt g2)

  many = Defs.manyD
  some = Defs.someD

instance (Defs g, Ord c, Enum c, Grammar c g) => Grammar c (Opt c g) where
  symb = OptSymb
  symbI = OptSymbI

unOptRules :: (Defs g, Grammar c g) => Rules (Opt c g) a -> Rules g a
-- unOptRules _ | trace "unOptRules" False = undefined
unOptRules (OptRulesOther r) = r
unOptRules (OptLifted p) = lift (unOpt p)
unOptRules (OptRulesPair p1 p2) = pairRules (unOptRules p1) (unOptRules p2)

instance (Defs g, Ord c, Enum c, Grammar c g) => Defs (Opt c g) where
  data Rules (Opt c g) a where
    OptRulesOther :: Rules g a -> Rules (Opt c g) a
    OptLifted :: Opt c g a -> Rules (Opt c g) (T a)
    OptRulesPair :: Rules (Opt c g) a -> Rules (Opt c g) b -> Rules (Opt c g) (a :*: b)

  --  lift _ | trace "lift" False = undefined
  lift p = OptLifted p

  --  unlift _ | trace "unlift" False = undefined
  unlift (OptLifted p) = p
  unlift (OptRulesOther r) = OptOther $ unlift r

  --  pairRules _ _ | trace "pairRules" False = undefined
  pairRules p1 p2 = OptRulesPair p1 p2

  --  unpairRules _ _ | trace "unpairRules" False = undefined
  unpairRules (OptRulesPair p1 p2) k = k p1 p2
  unpairRules p k = OptRulesOther $ unpairRules (unOptRules p) $ \x y -> unOptRules $ k (OptRulesOther x) (OptRulesOther y)

  -- letr h = OptRulesOther $ letr $ \a -> unOptRules $ h (OptSimple a)
  letr h =
    case h (OptOther empty) of
      OptRulesPair (OptLifted res) _
        | isSimpleEnough res ->
          let ~(OptRulesPair _ r) = h res in r
      _ -> OptRulesOther $ letr $ \a -> unOptRules $ h (OptSimple a)

-- >>> pprGrammar $  unlift $ letr $ \a -> pairRules (lift $ symb 'c') (lift a)
-- ↓(let rec N1 = ↑'c' in ↑N1)

newtype ThawSpace g a = ThawSpace {runThawSpace :: g ExChar -> g ExChar -> g a}

instance Functor g => Functor (ThawSpace g) where
  fmap f x = ThawSpace $ \sp sps -> fmap f (runThawSpace x sp sps)

instance Applicative g => Applicative (ThawSpace g) where
  pure a = ThawSpace $ \_ _ -> pure a
  f <*> g = ThawSpace $ \sp sps -> runThawSpace f sp sps <*> runThawSpace g sp sps

instance (Defs g, Alternative g) => Alternative (ThawSpace g) where
  empty = ThawSpace $ \_ _ -> empty
  f <|> g = ThawSpace $ \sp sps -> runThawSpace f sp sps <|> runThawSpace g sp sps

  many = Defs.manyD
  some = Defs.someD

instance (Defs g, Grammar Char g) => Grammar ExChar (ThawSpace g) where
  symb Space = ThawSpace $ \sp _ -> sp
  symb Spaces = ThawSpace $ \_ sps -> sps
  symb (NormalChar c) = ThawSpace $ \_ _ -> NormalChar <$> symb c

  symbI cs = ThawSpace $ \sp sps ->
    let r1 = if RS.member Space cs then sp else empty
        r2 = if RS.member Spaces cs then sps else empty
        r3 =
          let rs = RS.toRangeList $ RS.delete Space $ RS.delete Spaces cs
           in fmap fromChar $
                symbI $
                  RS.fromNormalizedRangeList $ map (\(NormalChar a1, NormalChar a2) -> (a1, a2)) rs
     in r1 <|> r2 <|> r3

  constantResult f a = ThawSpace $ \sp sps -> constantResult f (runThawSpace a sp sps)

instance Defs g => Defs (ThawSpace g) where
  newtype Rules (ThawSpace g) a = ThawSpaces {runThawSpaces :: g ExChar -> g ExChar -> Rules g a}

  lift a = ThawSpaces $ \sp sps -> lift (runThawSpace a sp sps)
  unlift a = ThawSpace $ \sp sps -> unlift (runThawSpaces a sp sps)

  pairRules x y = ThawSpaces $ \sp sps -> pairRules (runThawSpaces x sp sps) (runThawSpaces y sp sps)

  unpairRules xy k = ThawSpaces $ \sp sps ->
    unpairRules (runThawSpaces xy sp sps) $ \x y ->
      let x' = ThawSpaces $ \_ _ -> x
          y' = ThawSpaces $ \_ _ -> y
       in runThawSpaces (k x' y') sp sps

  letr k = ThawSpaces $ \sp sps ->
    letr $ \a -> runThawSpaces (k $ ThawSpace $ \_ _ -> a) sp sps

thawSpace :: (Defs exp, Alternative exp) => exp () -> ThawSpace exp a -> exp a
thawSpace sp0 g = unlift $
  letr $ \sp -> pairRules (lift $ Space <$ sp0) $
    letr $ \sps -> pairRules (lift $ Spaces <$ many sp) $ lift $ runThawSpace g sp sps

-- type Q = Int

-- data Transducer inc outc
--   = Transducer
--       Q -- init state
--       [Q] -- all the states
--       [Q] -- final states
--       (Trans inc outc)

-- data Trans inc outc
--   = Trans
--       (Q -> inc -> ([outc], Q)) -- transitions
--       (Q -> Maybe [outc]) -- final rules

-- finalProd :: Q -> Trans inc outc -> Maybe [outc]
-- finalProd q (Trans _ f) = f q

-- transTo :: Q -> inc -> Trans inc outc -> ([outc], Q)
-- transTo qi c (Trans tr _) = tr qi c

-- FIXME: will be replaced by Map2
newtype Memo env g = Memo {lookupMemo :: forall a. Qsp -> Qsp -> Var env a -> Maybe (g a)}

emptyMemo :: Memo env g
emptyMemo = Memo $ \_ _ _ -> Nothing

updateMemo :: Memo env g -> Qsp -> Qsp -> Var env a -> g a -> Memo env g
updateMemo (Memo f) q1 q2 x k =
  Memo $ \q1' q2' x' ->
    case E.eqVar x x' of
      Just Refl | q1 == q1', q2 == q2' -> Just k
      _ -> f q1' q2' x'

data Qsp = Qn | Qs | Qss deriving (Eq, Ord)

optSpaces :: forall g t. (Defs g, Grammar ExChar g) => FlatGrammar ExChar t -> g t
optSpaces (FlatGrammar (defs :: Bindings inc env env) rhs) =
  unlift $
    let m = forM allStates $ \qf -> do
          g <- procRHS Qn qf rhs
          return $ nt g <* finalProd qf
     in runM (asum <$> m) emptyMemo $ \a _ -> lift a
  where
    allStates = [Qn, Qs, Qss]

    finalProd Qn = pure ()
    finalProd Qs = () <$ symb Space
    finalProd Qss = () <$ symb Spaces

    transTo Qn Space = (pure Space, Qs)
    transTo Qn Spaces = (pure Spaces, Qss)
    transTo Qn (NormalChar c) = (char c, Qn)
    transTo Qs Space = (symb Space, Qs)
    transTo Qs Spaces = (symb Space, Qss)
    transTo Qs (NormalChar c) = (symb Space *> char c, Qn)
    transTo Qss Space = (symb Space, Qss)
    transTo Qss Spaces = (pure Spaces, Qss)
    transTo Qss (NormalChar c) = (symb Space *> char c, Qn)

    toM :: (forall r. DefType r => Memo env g -> ((a -> Memo env g -> Rules g r) -> Rules g r)) -> StateT (Memo env g) (DefM g) a
    toM f = StateT $ \memo -> DefM $ \k -> f memo (curry k)

    runM :: StateT (Memo env g) (DefM g) a -> (forall r. DefType r => Memo env g -> ((a -> Memo env g -> Rules g r) -> Rules g r))
    runM m memo k = unDefM (runStateT m memo) $ uncurry k

    procRHS :: Qsp -> Qsp -> RHS inc env a -> StateT (Memo env g) (DefM g) (Rules g (T a))
    procRHS q1 q2 (RHS ps) = fmap (lift . asum) $
      forM ps $ \p -> do
        g <- procProd q1 q2 p
        return (nt g)

    procProd :: Qsp -> Qsp -> Prod inc env a -> StateT (Memo env g) (DefM g) (Rules g (T a))
    procProd q1 q2 (PNil a)
      | q1 == q2 = return (lift (pure a))
      | otherwise = return (lift empty)
    procProd q1 q2 (PCons (SymbI cs) r) = do
      r1 <- if RS.member Space cs then procProd q1 q2 (PCons (Symb Space) r) else pure (lift empty)
      r2 <- if RS.member Spaces cs then procProd q1 q2 (PCons (Symb Spaces) r) else pure (lift empty)
      r3 <- do
        let cs' = RS.delete Space $ RS.delete Spaces cs
        let o = case q1 of
              Qn -> symbI cs'
              Qs -> symb Space *> symbI cs'
              Qss -> symb Spaces *> symbI cs'
        rr <- procProd Qn q2 r
        return $ (\a f -> f a) <$> o <*> nt rr
      return (lift $ nt r1 <|> nt r2 <|> r3)

    -- fmap (lift . asum) $
    -- forM nexts $ \(qm, oss) -> do
    --   g <- procProd qm q2 r
    --   let go = asum $ map (\(os, c) -> c <$ symbols os) oss
    --   return $ (\a k -> k a) <$> go <*> nt g
    -- where
    --   nexts :: [(Qsp, [([outc], inc)])]
    --   nexts = Map.toList $ foldr (\a -> let (os, qm) = transTo q1 a trans in Map.insertWith (++) qm [(os, a)]) Map.empty $ RS.toList cs
    procProd q1 q2 (PCons (Symb c) r) = do
      let (os, qm) = transTo q1 c
      g <- procProd qm q2 r
      return $ lift $ (\a k -> k a) <$> os <*> nt g
    procProd q1 q2 (PCons (NT x) r) =
      fmap (lift . asum) $
        forM allStates $ \qm -> do
          g1 <- toM (procVar q1 qm x)
          g2 <- procProd qm q2 r
          return $ (\a k -> k a) <$> nt g1 <*> nt g2

    -- Memo env g -> ((Rules g (T a) -> Memo env g -> Rules g r) -> Rules g r) is nothing but
    -- StateT (Memo env v) (DefM g) (Rules g r) so we must be able define it using monad I/F
    procVar :: DefType r => Qsp -> Qsp -> Var env a -> Memo env g -> ((Rules g (T a) -> Memo env g -> Rules g r) -> Rules g r)
    procVar q1 q2 x memo k =
      case lookupMemo memo q1 q2 x of
        Just r -> k (lift r) memo
        Nothing -> do
          let rhs = E.lookupEnv x defs
          letr $ \a ->
            runM (procRHS q1 q2 rhs) (updateMemo memo q1 q2 x a) $ \r memo' ->
              pairRules r (k r memo')

-- fuseWithTransducer :: forall g outc inc aaa. Enum inc => GrammarD outc g => FlatGrammar inc aaa -> Transducer inc outc -> g aaa
-- fuseWithTransducer (FlatGrammar (defs :: Bindings inc env env) rhs) (Transducer qinit qstates qfinals trans) =
--   unlift $
--     let m = forM qfinals $ \qf -> do
--           g <- procRHS qinit qf rhs
--           let Just os = finalProd qf trans
--           return $ nt g <* symbols os
--      in runM (asum <$> m) emptyMemo $ \a _ -> lift a
--   where
--     toM :: (forall r. DefType r => Memo env g -> ((a -> Memo env g -> Rules g r) -> Rules g r)) -> StateT (Memo env g) (DefM g) a
--     toM f = StateT $ \memo -> DefM $ \k -> f memo (curry k)

--     runM :: StateT (Memo env g) (DefM g) a -> (forall r. DefType r => Memo env g -> ((a -> Memo env g -> Rules g r) -> Rules g r))
--     runM m memo k = unDefM (runStateT m memo) $ uncurry k

--     procRHS :: Q -> Q -> RHS inc env a -> StateT (Memo env g) (DefM g) (Rules g (T a))
--     procRHS q1 q2 (RHS ps) = fmap (lift . asum) $
--       forM ps $ \p -> do
--         g <- procProd q1 q2 p
--         return (nt g)

--     procProd :: Q -> Q -> Prod inc env a -> StateT (Memo env g) (DefM g) (Rules g (T a))
--     procProd q1 q2 (PNil a)
--       | q1 == q2 = return (lift (pure a))
--       | otherwise = return (lift empty)
--     procProd q1 q2 (PCons (SymbI cs) r) = fmap (lift . asum) $
--       forM nexts $ \(qm, oss) -> do
--         g <- procProd qm q2 r
--         let go = asum $ map (\(os, c) -> c <$ symbols os) oss
--         return $ (\a k -> k a) <$> go <*> nt g
--       where
--         nexts :: [(Q, [([outc], inc)])]
--         nexts = Map.toList $ foldr (\a -> let (os, qm) = transTo q1 a trans in Map.insertWith (++) qm [(os, a)]) Map.empty $ RS.toList cs
--     procProd q1 q2 (PCons (Symb c) r) = do
--       let (os, qm) = transTo q1 c trans
--       g <- procProd qm q2 r
--       return $ lift $ (\_ k -> k c) <$> symbols os <*> nt g
--     procProd q1 q2 (PCons (NT x) r) =
--       fmap (lift . asum) $
--         forM qstates $ \qm -> do
--           g1 <- toM (procVar q1 qm x)
--           g2 <- procProd qm q2 r
--           return $ (\a k -> k a) <$> nt g1 <*> nt g2

--     -- Memo env g -> ((Rules g (T a) -> Memo env g -> Rules g r) -> Rules g r) is nothing but
--     -- StateT (Memo env v) (DefM g) (Rules g r) so we must be able define it using monad I/F
--     procVar :: DefType r => Q -> Q -> Var env a -> Memo env g -> ((Rules g (T a) -> Memo env g -> Rules g r) -> Rules g r)
--     procVar q1 q2 x memo k =
--       case lookupMemo memo q1 q2 x of
--         Just r -> k (lift r) memo
--         Nothing -> do
--           let rhs = E.lookupEnv x defs
--           letr $ \a ->
--             runM (procRHS q1 q2 rhs) (updateMemo memo q1 q2 x a) $ \r memo' ->
--               pairRules r (k r memo')

-- collapseSpacer :: Transducer ExChar ExChar
-- collapseSpacer = Transducer 0 [0, 1, 2] [0, 1, 2] (Trans trC trF)
--   where
--     -- This transducer is to rearrange a sequence of S and S* into a normal form; e.g., S S* S S* -> S S S*.

--     trC 0 Space = ([], 1)
--     trC 0 Spaces = ([], 2)
--     trC 0 (NormalChar c) = ([NormalChar c], 0)
--     -- Read space
--     trC 1 Space = ([Space], 1)
--     trC 1 Spaces = ([Space], 2)
--     trC 1 (NormalChar c) = ([Space, NormalChar c], 0)
--     -- Read spaces
--     trC 2 Space = ([Space], 2)
--     trC 2 Spaces = ([], 2)
--     trC 2 (NormalChar c) = ([Spaces, NormalChar c], 0)
--     trC _ _ = error "Cannot happen"

--     trF 0 = Just []
--     trF 1 = Just [Space]
--     trF 2 = Just [Spaces]
--     trF _ = error "Cannot happen"

collapseSpace :: (Defs g, Grammar ExChar g) => FlatGrammar ExChar a -> g a
collapseSpace = optSpaces --  fuseWithTransducer g collapseSpacer

withSpace :: (Defs exp, Grammar Char exp) => exp () -> ToFlatGrammar ExChar a -> exp a
withSpace gsp g = thawSpace gsp $ simplifyGrammar $ collapseSpace (flatten g)
