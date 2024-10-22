{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

-- | This module provides manipulation of grammars.
module Text.FliPpr.Grammar
  ( -- * Type definitions
    FromSymb(..), Grammar,
    GrammarD,
    ExChar (..),
    CharLike (..),
    Simplify,

    -- * Derived combinators
    char,
    symbols,
    text,
    space,
    spaces,

    rule, nt,

    -- * Manipulation of Grammars
    simplifyGrammar,
    withSpace,

    -- ** Flat Grammars
    SemToFlatGrammar,
    flatten,
    Prod (..),
    Symb (..),
    RHS (..),
    FlatGrammar (..),
    E.EnvImpl (..),

    -- * Pretty-Printing
    pprGrammar,
    pprAsFlat,

    -- * Re-export of 'Defs' for convenience.
    module Defs,
  )
where

import           Control.Applicative       (Alternative (..), Const (..))
import           Control.Arrow             (second)
import           Control.Category          (Category (..), id, (.), (>>>))
import           Control.Monad             (forM, void)
import           Control.Monad.State       (MonadState, State, StateT (..),
                                            evalState, evalStateT, get, put)
import           Data.Foldable             (asum)
--



import           Data.Bifunctor            (bimap)

import           Data.Coerce               (coerce)
import           Data.Maybe                (mapMaybe)
import           Data.Monoid               (Endo (..))
import           Data.Proxy                (Proxy (Proxy))
import           Data.RangeSet.List        (RSet)
import qualified Data.RangeSet.List        as RS
import           Data.Typeable             ((:~:) (..))
import           Prelude                   hiding (id, (.))
import qualified Text.FliPpr.Doc           as D
import           Text.FliPpr.Internal.Defs as Defs
import qualified Text.FliPpr.Internal.Env  as E

-- import Debug.Trace (trace)
-- import Text.Printf (printf)

{-# ANN module "HLint: ignore Use const" #-}

class FromSymb c e | e -> c where
  -- | A production of a given single char.
  symb :: c -> e c
  symb = symbI . RS.singleton

  -- | A production of a single character taken from a given set.
  symbI :: RSet c -> e c

-- | A grammar expression. This class does not specify any ways to define "nonterminals", which indeed is the role of 'Defs'.
type Grammar c e = (Applicative e, Alternative e, FromSymb c e)

-- class (Applicative e, Alternative e) => Grammar c e | e -> c where


-- | A production of symbols.
symbols :: Grammar c e => [c] -> e [c]
symbols = foldr (\a r -> (:) <$> symb a <*> r) (pure [])

-- | Grammars, with ability to define nonterminals.
type GrammarD c e = (Defs e, Grammar c e)

newtype NonterminalPrinterM c a = NonterminalPrinterM {runNonterminalPrinterM :: State Int a}
  deriving newtype (Functor, Applicative, Monad, MonadState Int)

instance Defs.VarM (NonterminalPrinterM c) where
  newVar = do
    i <- get
    put $! i + 1
    return $ "N" ++ show i
  {-# INLINE newVar #-}

  nestScope = id
  {-# INLINE nestScope #-}

instance Functor (PprExp (NonterminalPrinterM c)) where
  fmap _ (PprExp h) = PprExp h
  {-# INLINE fmap #-}

deriving newtype instance Functor (Norm (PprExp (NonterminalPrinterM c)))
instance Applicative (PprExp (NonterminalPrinterM c)) where
  pure _ = PprExp $ \_ -> return $ D.text "ε"
  {-# INLINE pure #-}

  f <*> a = PprExp $ \k -> (\d1 d2 -> D.parensIf (k > 9) $ d1 D.<+> D.align d2) <$> pprExp f 9 <*> pprExp a 10
  {-# INLINE (<*>) #-}

deriving newtype instance Applicative (Norm (PprExp (NonterminalPrinterM c)))

instance Alternative (Norm (PprExp (NonterminalPrinterM c))) where
  empty = PprExpN $ \_ -> return $ D.text "⊥"
  {-# INLINE empty #-}
  f <|> g = PprExpN $ \k -> (\d1 d2 -> D.parensIf (k > 3) $ D.sep [d1, D.text "|", d2]) <$> pprExpN f 3 <*> pprExpN g 3
  {-# INLINE (<|>) #-}

  many = Defs.manyD
  {-# INLINE many #-}
  some = Defs.someD
  {-# INLINE some #-}


instance Show c => FromSymb c (PprExp (NonterminalPrinterM c)) where
  symb c = PprExp $ \_ -> return $ D.text (show c)
  {-# INLINE symb #-}
  symbI cs = PprExp $ \_ -> return $ D.text (show cs)
  {-# INLINE symbI #-}

deriving newtype instance Show c => FromSymb c (Norm (PprExp (NonterminalPrinterM c)))

pprGrammar :: Norm (PprExp (NonterminalPrinterM c)) a -> D.Doc
pprGrammar g =
  evalState (runNonterminalPrinterM (pprExpN g 0)) 1

-- | 'rule' introduces sharing. A typical use is:
--
-- > do x <- rule $ text "A" <|> text "B"
-- >   ... nt x ... nt x ...
--
--
-- This code is different from the below one, which expands the definition of @x@.
--
-- > do x <- return $ text "A" <|> text "B"
-- >    ... x ... x ...
--
-- Note that this combinator is just about sharing. Looping must be handled by
-- 'letr' and its derived combinators (such as 'mfixDefM'; recursive definitions
-- is possible by locally defining @mfix = mfixDefM@ together with
-- GHC extensions "RebindableSyntax" and "RecursiveDo").

rule :: Defs.Defs f => f a -> DefM f (Tip (f a))
rule = coerce . Defs.share

-- | A synonym of 'runIdentity', which is named after "nonterminal" and supposed to be used with 'rule'.
nt :: Tip (f a) -> f a
nt = coerce

-- | Characters with special symbols 'Space' and 'Spaces'. They will be
--   converted to a single "white space" and zero-or-more "white spaces", by
--   'withSpace' so that concatenation of 'Space' and 'Spaces' does not lead to
--   ambiguity. The "white space" here is not necessarily the space character,
--   'withSpace' provides users to specify how "white spaces" are interpreted.
data ExChar
  = Space    -- ^ Special symbol denoting a single space " "
  | Spaces   -- ^ Special symbol denoting zero-or-more spaces
  | NormalChar {-# UNPACK #-} !Char -- ^ Normal charactors (which may be " ")
  deriving stock (Eq, Ord)

instance Enum ExChar where
  toEnum 0 = Space
  toEnum 1 = Spaces
  toEnum n = NormalChar (toEnum $! n -2)

  fromEnum Space          = 0
  fromEnum Spaces         = 1
  fromEnum (NormalChar c) = fromEnum c + 2

  succ Space          = Spaces
  succ Spaces         = NormalChar minBound
  succ (NormalChar c) = NormalChar (succ c)

  pred Spaces = Space
  pred (NormalChar c)
    | c == minBound = Spaces
    | otherwise = NormalChar (pred c)
  pred Space = error "pred: no predecessor"

instance D.Pretty ExChar where
  ppr (NormalChar c) = D.ppr c
  ppr Space          = D.text "_"
  ppr Spaces         = D.text "<spaces>"

  pprList = uncurry pprList' . chars []
    where
      chars s (NormalChar c : cs) = chars (c : s) cs
      chars s r                   = (reverse s, r)

      pprList' [] [] = D.text ""
      pprList' [] (c : cs) = case cs of [] -> D.ppr c; _ -> D.ppr c D.<+> D.pprList cs
      pprList' s [] = D.ppr s
      pprList' s r = D.ppr s D.<+> D.pprList r

instance Show ExChar where
  show = show . D.ppr
  showList s r = show (D.pprList s) ++ r

class CharLike c where
  -- | Injection from 'Char'
  fromChar :: Char -> c

instance CharLike Char where
  fromChar = id

instance CharLike ExChar where
  fromChar = NormalChar

-- | A production of a charactor.
char :: (CharLike c, Grammar c e) => Char -> e c
char c = symb (fromChar c)

-- | A production of a string.
text :: (CharLike c, Grammar c e) => String -> e [c]
text = foldr (\c r -> (:) <$> char c <*> r) (pure [])

-- | A production of the special symbol 'Space'
space :: Grammar ExChar e => e ()
space = void (symb Space)

-- | A production of the special symbol 'Spaces'
spaces :: Grammar ExChar e => e ()
spaces = void (symb Spaces)

type Env = E.Env E.U

type Var = E.Var E.U

type Bindings c env1 env2 = Env (RHS c env1) env2

newtype RHS c env a = RHS [Prod c env a]
  deriving stock Functor

instance Show c => D.Pretty (RHS c env a) where
  ppr (RHS rs) =
    D.punctuate (D.line D.<> D.text "|" D.<> D.text " ") $ map D.ppr rs

-- | Flat grammars. This definion basically follows what appears in:
--   Arthur I. Baars, S. Doaitse Swierstra, Marcos Viera: Typed Transformations of Typed Grammars: The Left Corner Transform. Electron. Notes Theor. Comput. Sci. 253(7): 51-64 (2010).
data FlatGrammar c a = forall env. FlatGrammar !(Bindings c env env) !(RHS c env a)

pprAsFlat :: Show c => SemToFlatGrammar c a -> D.Doc
pprAsFlat = D.ppr . flatten

instance Show c => D.Pretty (FlatGrammar c a) where
  ppr (FlatGrammar bs r) =
    D.align (E.pprEnv pprDef bs D.</> pprDefN (D.text "Start") r)
    where
      pprDef x rhs = D.text ("N" ++ x) D.<+> D.group (D.align (D.text "=" D.<+> D.ppr rhs))
      pprDefN n rhs = D.hsep [n, D.text "=", D.align (D.ppr rhs)]

data Prod c env a = PNil !a | forall b. PCons !(Symb c env b) !(Prod c env (b -> a))

instance Show c => D.Pretty (Prod c env a) where
  ppr (PNil _) = D.text "ε"
  ppr (PCons s r) = go (D.ppr s) r
    where
      go :: forall b. D.Doc -> Prod c env b -> D.Doc
      go d (PNil _)      = d
      go d (PCons ss rr) = d D.<+> go (D.ppr ss) rr

instance Functor (Prod c env) where
  fmap f (PNil a)    = PNil (f a)
  fmap f (PCons s r) = PCons s (fmap (f .) r)


data Symb c env a where
  NT :: !(Var env a) -> Symb c env a
  Symb :: !c -> Symb c env c
  SymbI :: !(RSet c) -> Symb c env c

instance Show c => D.Pretty (Symb c env a) where
  ppr (NT x)     = D.text ("N" ++ E.showVar x)
  ppr (Symb c)   = D.text (show c)
  ppr (SymbI cs) = D.text (show cs)

instance E.Shiftable E.U (Symb c) where
  shift diff (NT x)  = NT (E.shift diff x)
  shift _ (Symb c)   = Symb c
  shift _ (SymbI cs) = SymbI cs

instance E.Shiftable E.U (Prod c) where
  shift _ (PNil a)       = PNil a
  shift diff (PCons s r) = PCons (E.shift diff s) $ E.shift diff r

instance E.Shiftable E.U (RHS c) where
  shift diff (RHS rs) = RHS $ map (E.shift diff) rs

-- type Diff env env' = E.VarT E.U env env'

-- -- This implementation can be a source of slowdown due to shifting, but we did
-- -- not find this is a bottleneck by test cases in @./examples/@.
-- data Res c env a = forall env'. Res (Bindings c env' env') (RHS c env' a) (Diff env env')

-- instance Functor (Res c env) where
--   fmap f (Res bs rhs diff) = Res bs (fmap f rhs) diff

instance Applicative (Prod c env) where
  pure = PNil
  (<*>) = go id
    where
      -- Derived from the following definition.
      -- PNil a <*> f = fmap a f
      -- PCons a as <*> r = PCons a (flip <$> as <*> r)
      go :: (a -> b -> r) -> Prod c env a -> Prod c env b -> Prod c env r
      go f (PNil a) r     = fmap (f a) r
      go f (PCons a as) r = PCons a (go (flip . (f .)) as r)

data CondRHS = Empty | Singleton | Other

data SCondRHS (c :: CondRHS) where
  SEmpty     :: SCondRHS 'Empty
  SSingleton :: SCondRHS 'Singleton
  SOther     :: SCondRHS 'Other

data RHSs c env (b :: CondRHS) a where
  EmptyRHS :: RHSs c env 'Empty a
  SingRHS  :: !(Prod c env a) -> RHSs c env 'Singleton  a
  OtherRHS :: ![Prod c env a] ->  RHSs c env 'Other a

instance Functor (RHSs c env b) where
  fmap _ EmptyRHS      = EmptyRHS
  fmap f (SingRHS p)   = SingRHS (fmap f p)
  fmap f (OtherRHS ps) = OtherRHS $ map (fmap f) ps

toRHS :: RHSs c env b a -> RHS c env a
toRHS = RHS . toProds

toProds :: RHSs c env b a -> [Prod c env a]
toProds EmptyRHS         = []
toProds (SingRHS prod)   = [prod]
toProds (OtherRHS prods) = prods

-- | Interpretation of the 'GrammarD' methods to produce 'FlatGrammar's.

newtype SemToFlatGrammar c a =
  SemToFlatGrammar { unSemToFlatGrammar :: forall env. E.Rep E.U env -> SemToFlatGrammarRes c env a }
  deriving stock Functor

data SemToFlatGrammarRes c env a =
  forall env' b.
  SemToFlatGrammarRes !(E.Rep E.U env')      -- Representation of the type of resulting environment
                      !(E.VarT E.U env env') -- A witness that result is bigger than the original
                      !(SCondRHS b)          -- A condition that a resulting rhs should satisfy
                      !(forall envf. E.VarT E.U env' envf -- A final environment
                        -> E.Env E.U (RHS c envf) env     -- The original environment
                        -> (E.Env E.U (RHS c envf) env' , RHSs c envf b a))

instance Functor (SemToFlatGrammarRes c env) where
  fmap f (SemToFlatGrammarRes tenv diff cond k) =
    SemToFlatGrammarRes tenv diff cond (\diff' env -> second (fmap f) $ k diff' env)

toFlatGrammar :: SemToFlatGrammar c a -> FlatGrammar c a
toFlatGrammar d =
  case unSemToFlatGrammar d E.emptyRep of
    SemToFlatGrammarRes _ _ _ k ->
      let (env, r) = k id E.emptyEnv
      in FlatGrammar env (toRHS r)

instance Applicative (SemToFlatGrammar c) where
  pure a = SemToFlatGrammar $ \tenv -> SemToFlatGrammarRes tenv id SSingleton (\_diff env -> (env, SingRHS $ PNil a))
  d1 <*> d2 = SemToFlatGrammar $ \tenv ->
    case unSemToFlatGrammar d1 tenv of
      SemToFlatGrammarRes tenv1 diff1 cond1 k1 ->
        case unSemToFlatGrammar d2 tenv1 of
          SemToFlatGrammarRes tenv2 diff2 cond2 k2 ->
            case (cond1, cond2) of
              (SEmpty, _) -> SemToFlatGrammarRes tenv id SEmpty $ \_ env -> (env, EmptyRHS)
              (_, SEmpty) -> SemToFlatGrammarRes tenv id SEmpty $ \_ env -> (env, EmptyRHS)
              (SSingleton, SSingleton) ->
                SemToFlatGrammarRes tenv2 (diff1 >>> diff2) SSingleton $ \df env ->
                  let (env1, SingRHS p1) = k1 (diff2 >>> df) env
                      (env2, SingRHS p2) = k2 df env1
                  in (env2, SingRHS (p1 <*> p2))
              _ ->
                SemToFlatGrammarRes (tenv2 `E.extendRep` Proxy `E.extendRep` Proxy) (E.diffStep (E.diffStep (diff1 >>> diff2))) SSingleton $ \df env ->
                  let (env1 , r1) = k1 (E.diffStep (E.diffStep diff2) >>> df) env
                      (env2 , r2) = k2 (E.diffStep (E.diffStep E.diffRefl) >>> df) env1
                      (env3, x1, _) = E.extendEnv env2 (toRHS r1)
                      (env4, x2, _) = E.extendEnv env3 (toRHS r2)
                  in (env4, SingRHS $ PCons (NT $ E.shift (E.diffStep E.diffRefl >>> df) x1) $ PCons (NT $ E.shift df x2) $ PNil (\x f -> f x))

instance Alternative (SemToFlatGrammar c) where
  empty = SemToFlatGrammar $ \tenv -> SemToFlatGrammarRes tenv id SEmpty (\_diff env -> (env, EmptyRHS))
  d1 <|> d2 = SemToFlatGrammar $ \tenv ->
    case unSemToFlatGrammar d1 tenv of
      SemToFlatGrammarRes tenv1 diff1 cond1 k1 ->
        case unSemToFlatGrammar d2 tenv1 of
          SemToFlatGrammarRes tenv2 diff2 cond2 k2 ->
            case (cond1, cond2) of
              (SEmpty, _) -> SemToFlatGrammarRes tenv2 (diff1 >>> diff2) cond2 $ \df env ->
                              let (env1, _) = k1 (diff2 >>> df) env
                                  (env2, r2) = k2 df env1
                              in (env2, r2)
              (_, SEmpty) -> SemToFlatGrammarRes tenv2 (diff1 >>> diff2) cond1 $ \df env ->
                              let (env1, r1) = k1 (diff2 >>> df) env
                                  (env2, _) = k2 df env1
                              in (env2, r1)
              _ -> SemToFlatGrammarRes tenv2 (diff1 >>> diff2) SOther $ \df env ->
                              let (env1, r1) = k1 (diff2 >>> df) env
                                  (env2, r2) = k2 df env1
                              in (env2, OtherRHS $ toProds r1 ++ toProds r2 )



  many = Defs.manyD
  some = Defs.someD

instance FromSymb c (SemToFlatGrammar c) where
  symb c = SemToFlatGrammar $ \tenv -> SemToFlatGrammarRes tenv id SSingleton (\_ env -> (env, SingRHS $ PCons (Symb c) $ PNil id))
  symbI cs = SemToFlatGrammar $ \tenv -> SemToFlatGrammarRes tenv id SSingleton (\_ env -> (env, SingRHS $ PCons (SymbI cs) $ PNil id))

data DCond bs br as ar where
  DCondT    :: !(SCondRHS c) -> DCond '[] c '[] a
  DCondCons :: !(SCondRHS c) -> !(DCond rbs rb ras ra) -> DCond (c ': rbs) rb (a ': ras) ra

data DRHS c env bs br as ar where
  DRHST    :: !(RHSs c env b a) -> DRHS c env '[] b '[] a
  DRHSCons :: !(RHSs c env b a) -> !(DRHS c env bs br as ar) -> DRHS c env (b ': bs) br (a ': as) ar

data DSemToFlatGrammarRes c env as a =
  forall env' bs b.
  DSemToFlatGrammarRes !(E.Rep E.U env')
                       !(E.VarT E.U env env')
                       !(DCond bs b as a)
                       !(forall envf. E.VarT E.U env' envf
                         -> E.Env E.U (RHS c envf) env
                         -> (E.Env E.U (RHS c envf) env' , DRHS c envf bs b as a))

instance Defs (SemToFlatGrammar c) where
  newtype D (SemToFlatGrammar c) as a =
    DSemToFlatGrammar { unDSemToFlatGrammar :: forall env. E.Rep E.U env -> DSemToFlatGrammarRes c env as a }

  liftD d = DSemToFlatGrammar $ \tenv ->
    case unSemToFlatGrammar d tenv of
      SemToFlatGrammarRes tenv1 diff1 cond1 k1 ->
        DSemToFlatGrammarRes tenv1 diff1 (DCondT cond1) $ \df env -> second DRHST (k1 df env)

  unliftD d = SemToFlatGrammar $ \tenv ->
    case unDSemToFlatGrammar d tenv of
      DSemToFlatGrammarRes tenv1 diff1 (DCondT cond1) k1 ->
        SemToFlatGrammarRes tenv1 diff1 cond1 $ \df env -> second (\case { DRHST x -> x }) (k1 df env)


  consD d ds = DSemToFlatGrammar $ \tenv ->
    case unSemToFlatGrammar d tenv of
      SemToFlatGrammarRes tenv1 diff1 cond1 k1 ->
        case unDSemToFlatGrammar ds tenv1 of
          DSemToFlatGrammarRes tenv2 diff2 cond2 k2 ->
            DSemToFlatGrammarRes tenv2 (diff1 >>> diff2) (DCondCons cond1 cond2) $ \df env ->
              let (env1, r1) = k1 (diff2 >>> df) env
                  (env2, r2) = k2 df env1
              in (env2, DRHSCons r1 r2)

  letrD h = DSemToFlatGrammar $ \tenv ->
    let  tenva = E.extendRep tenv Proxy
         harg = SemToFlatGrammar $ \tenv' -> SemToFlatGrammarRes tenv' E.diffRefl SSingleton $ \df env ->
                  (env , SingRHS $ PCons (NT $ E.shift (E.diffRep tenva tenv' >>> df) (E.varZ tenv)) $ PNil id )
    in case unDSemToFlatGrammar (h harg) tenva of
          DSemToFlatGrammarRes tenvh diffh (DCondCons _ condh) kh ->
            DSemToFlatGrammarRes tenvh (E.diffStep E.diffRefl >>> diffh) condh $ \df env ->
              let (env', x, _) = E.extendEnv env (RHS [])
              in case kh df env' of
                (envh, DRHSCons rh r) -> (E.updateEnv (E.shift diffh x) (toRHS rh) envh, r)




-- -- | Interpretation of the 'GrammarD' methods to produce 'FlatGrammar's.

-- newtype ToFlatGrammar c a = ToFlatGrammar {toFlatGrammar :: forall env. Bindings c env env -> Res c env a}
--   deriving (Functor)

-- instance Applicative (Prod c env) where
--   pure = PNil
--   (<*>) = go id
--     where
--       -- Derived from the following definition.
--       -- PNil a <*> f = fmap a f
--       -- PCons a as <*> r = PCons a (flip <$> as <*> r)
--       go :: (a -> b -> r) -> Prod c env a -> Prod c env b -> Prod c env r
--       go f (PNil a) r     = fmap (f a) r
--       go f (PCons a as) r = PCons a (go (flip . (f .)) as r)

-- instance Applicative (ToFlatGrammar c) where
--   pure a = ToFlatGrammar $ \defs -> Res defs (RHS [PNil a]) id
--   f <*> a = ToFlatGrammar $ \defs ->
--     case toFlatGrammar f defs of
--       Res defs1 rhs1 diff1 ->
--         case toFlatGrammar a defs1 of
--           Res defs2 rhs2 diff2 ->
--             case (rhs1, rhs2) of
--               (RHS [], _) -> Res defs2 (RHS []) (diff2 . diff1)
--               (_, RHS []) -> Res defs2 (RHS []) (diff2 . diff1)
--               (RHS [p1], RHS [p2]) -> Res defs2 (RHS [E.shift diff2 p1 <*> p2]) (diff2 . diff1)
--               _ ->
--                 let (defs3, x, diff3) = E.extendEnv defs2 (E.shift diff2 rhs1)
--                     (defs4, y, diff4) = E.extendEnv (E.mapEnv (E.shift diff3) defs3) (E.shift diff3 rhs2)
--                  in Res (E.mapEnv (E.shift diff4) defs4) (RHS [PCons (NT $ E.shift diff4 x) (PNil id) <*> PCons (NT y) (PNil id)]) (diff4 . diff3 . diff2 . diff1)

-- instance Alternative (ToFlatGrammar c) where
--   empty = ToFlatGrammar $ \defs -> Res defs (RHS []) id
--   a1 <|> a2 = ToFlatGrammar $ \defs ->
--     case toFlatGrammar a1 defs of
--       Res defs1 (RHS ps1) diff1 ->
--         case toFlatGrammar a2 defs1 of
--           Res defs2 (RHS ps2) diff2 ->
--             Res defs2 (RHS (map (E.shift diff2) ps1 ++ ps2)) (diff2 . diff1)

--   many = Defs.manyD
--   some = Defs.someD

-- instance FromSymb c (ToFlatGrammar c) where
--   symb c = ToFlatGrammar $ \defs -> Res defs (RHS [PCons (Symb c) $ PNil id]) id
--   symbI cs = ToFlatGrammar $ \defs -> Res defs (RHS [PCons (SymbI cs) $ PNil id]) id

-- --  constantResult = (<$)

-- type Value = Defs.DTypeVal

-- -- valueMap :: (forall b. f b -> g b) -> Value f a -> Value g a
-- -- valueMap f (VT a)      = VT (f a)
-- -- valueMap f (VCons x y) = VCons (f x) (valueMap f y)

-- data Ress c env a = forall env'. Ress (Bindings c env' env') (Value (RHS c env') a) (Diff env env')

-- instance Defs (ToFlatGrammar c) where
--   newtype Fs (ToFlatGrammar c) a = ToFlatGrammars {toFlatGrammars :: forall env. Bindings c env env -> Ress c env a}

--   liftDS c = ToFlatGrammars $ \defs ->
--     case toFlatGrammar c defs of
--       Res defs' r' diff' -> Ress defs' (VT r') diff'

--   unliftDS c = ToFlatGrammar $ \defs ->
--     case toFlatGrammars c defs of
--       Ress defs' (VT r') diff' -> Res defs' r' diff'

--   consDS x y = ToFlatGrammars $ \defs -> case toFlatGrammar x defs of
--     Res defs1 r1 diff1 -> case toFlatGrammars y defs1 of
--       Ress defs2 r2 diff2 -> Ress defs2 (VCons (E.shift diff2 r1) r2) (diff2 . diff1)

--   letrDS h = ToFlatGrammars $ \defs ->
--     let (defs1, x, diff) = E.extendEnv defs (RHS []) -- a placeholder
--         argH = ToFlatGrammar $ \defs' -> let diff' = E.diffRep (E.repOf defs1) (E.repOf defs') in Res defs' (E.shift diff' $ RHS [PCons (NT x) $ PNil id]) id
--      in case toFlatGrammars (h argH) $ E.mapEnv (E.shift diff) defs1 of
--           Ress defs2 (VCons r res) diff2 ->
--             let defs2' = E.updateEnv (E.shift diff2 x) r defs2
--              in Ress defs2' res (diff2 . diff)

-- | Conversion to flat grammars.
flatten :: SemToFlatGrammar c a -> FlatGrammar c a
flatten = toFlatGrammar
  -- case toFlatGrammar g E.emptyEnv of
  --   Res defs r _ -> FlatGrammar defs r

-- checking productivity

removeNonProductive :: FlatGrammar c a -> FlatGrammar c a
removeNonProductive (FlatGrammar (defs :: Bindings c env0 env0) rhs) =
  -- trace (show $ D.text " " D.<> D.align (D.ppr $ FlatGrammar defs rhs)) $
  FlatGrammar (E.mapEnv procRHS defs) (procRHS rhs)
  where
    prodTable = check initTable

    initTable = E.mapEnv (const $ Const False) defs

    checkRHS :: Env (Const Bool) env' -> RHS c env' a -> Bool
    checkRHS env (RHS rs) = any (checkProd env) rs

    checkProd :: Env (Const Bool) env' -> Prod c env' a -> Bool
    checkProd _ (PNil _)      = True
    checkProd env (PCons s r) = checkSymb env s && checkProd env r

    checkSymb :: Env (Const Bool) env' -> Symb c env' a -> Bool
    checkSymb _ (Symb _)   = True
    checkSymb _ (SymbI cs) = not (RS.null cs)
    checkSymb env (NT x)   = getConst $ E.lookupEnv x env

    checkDefs :: Env (RHS c env') env -> Env (Const Bool) env' -> Env (Const Bool) env
    checkDefs es env = E.mapEnv (Const . checkRHS env) es

    -- pprMP mp = E.pprEnv (\s d -> D.hsep [D.text s, D.text "=", D.text (show $ getConst d)]) mp :: D.Doc

    check mp =
      let mp' = checkDefs defs mp
          flag = appEndo (getConst $ E.zipWithA (\(Const b1) (Const b2) -> Const $ Endo (\x -> x || (b1 /= b2))) mp mp') False
       in -- trace (show $ D.text "  " D.<> D.align (pprMP mp D.</> pprMP mp' D.</> D.text "flag: " D.<> D.text (show flag))) $
          if flag then check mp' else mp'

    procRHS :: RHS c env0 a -> RHS c env0 a
    procRHS (RHS rs) = RHS $ mapMaybe procProd rs

    procProd :: Prod c env0 a -> Maybe (Prod c env0 a)
    procProd (PNil a)    = return (PNil a)
    procProd (PCons s r) = PCons <$> procSymb s <*> procProd r

    procSymb :: Symb c env0 a -> Maybe (Symb c env0 a)
    procSymb (Symb c) = return (Symb c)
    procSymb (SymbI cs) = if RS.null cs then Nothing else return (SymbI cs)
    procSymb (NT x) = if getConst (E.lookupEnv x prodTable) then return (NT x) else Nothing

newtype MemoS g env = MemoS {lookupMemoS :: forall a. Var env a -> Maybe (g a)}

unFlatten :: forall c g r. (GrammarD c g) => FlatGrammar c r -> g r
unFlatten (FlatGrammar (defs :: Bindings c env env) rhs0) =
  local $ evalStateT (procRHS rhs0) initMemoS
  where
    initMemoS :: MemoS g env
    initMemoS = MemoS $ const Nothing

    updateMemoS :: MemoS g env -> Var env a -> g a -> MemoS g env
    updateMemoS (MemoS m) x v = MemoS $ \x' ->
      case E.eqVar x x' of
        Just Refl -> Just v
        Nothing   -> m x'

    procRHS :: RHS c env a -> StateT (MemoS g env) (DefM g) (g a)
    procRHS (RHS rs) = asum <$> mapM procProd rs

    procProd :: Prod c env a -> StateT (MemoS g env) (DefM g) (g a)
    procProd (PNil a) = return (pure a)
    procProd (PCons s r) = do
      s' <- procSymb s
      r' <- procProd r
      return $ (\a k -> k a) <$> s' <*> r'

    -- (fmap $ \a k -> k a) <$> procSymb s <*> procProd r

    -- x = rhs is inlinable if rhs is small enouch and x does not appear in rhs
    inlinable :: Var env a -> RHS c env a -> Bool
    inlinable _ (RHS []) = True
    inlinable x (RHS [p]) = smallEnough p && not (occur p)
      where
        smallEnough :: Prod c env b -> Bool
        smallEnough (PNil _)           = True
        smallEnough (PCons _ (PNil _)) = True
        smallEnough _                  = False

        occur :: Prod c env b -> Bool
        occur (PNil _) = False
        occur (PCons (NT y) _) | Just _ <- E.eqVar x y = True
        occur (PCons _ r) = occur r
    inlinable _ _ = False

    procSymb :: Symb c env a -> StateT (MemoS g env) (DefM g) (g a)
    procSymb (Symb c) = return (symb c)
    procSymb (SymbI cs) = return (symbI cs)
    procSymb (NT x) = StateT $ \memo ->
      case lookupMemoS memo x of
        Just r -> return (r, memo)
        Nothing -> do
          let rhs = E.lookupEnv x defs
          if inlinable x rhs
            then do -- FIXME: Is it OK to pass memo unchanged for performance?
                    (r, m) <- runStateT (procRHS rhs) memo
                    return (r, updateMemoS m x r)
            else letr1 $ \a -> do
                    (r, m) <- runStateT (procRHS rhs) (updateMemoS memo x a)
                    return (r, (a, m))



-- a simple optimizing interpretation
-- We use the property that
--
--   symb a <|> symb b = symbI (RS.singleton a `RS.union` RS.singleton b)
--
-- Also we perform simple inlining: For h :: (a -> a * r) -> r, if e1 of
--    <e1, e2> = h (Complex a)
-- is still simple, we can replace it with (snd . h) e1

data Opt c g a where
  OptSymb :: !c -> Opt c g c
  OptSymbI :: !(RSet c) -> Opt c g c
  OptEmpty :: Opt c g a
  OptPure :: a -> Opt c g a
  -- OptSimple :: g a -> Opt c g a -- inlinable
  OptOther :: !(g a) -> Opt c g a

-- | An interpretation of grammar methods for simplification.

-- type Simplify c g = CheckProd c (Opt c g)
type Simplify c g = Opt c (SemToFlatGrammar c)

-- | Simplification of grammars, it performs
--
--   * Conversions using the fact that @empty@ is the zero element
--
--   * Conversions using the fact that @pure f@ is the unit element
--
--   * Merging 'symbI's that occur directly under '<|>'
--
--   * Removal of nonterminals unreachable from the start symbol.
--
--   * A simple inlining.

simplifyGrammar :: (Ord c, Enum c, GrammarD c g) => Simplify c g a -> g a
simplifyGrammar g = unOpt $ unFlatten $ removeNonProductive $ flatten $ unOpt g

unOpt :: Grammar c g => Opt c g a -> g a
unOpt (OptSymb c)   = symb c
unOpt (OptSymbI cs) = symbI cs
unOpt OptEmpty      = empty
unOpt (OptPure a)   = pure a
-- unOpt (OptSimple p) = p
unOpt (OptOther p)  = p

-- isSimpleEnough :: Opt c g a -> Bool
-- isSimpleEnough (OptOther _) = False
-- isSimpleEnough _            = True

instance Grammar c g => Functor (Opt c g) where
  fmap f (OptPure a) = OptPure (f a)
  fmap _ OptEmpty    = OptEmpty
  fmap f p           = OptOther $ fmap f (unOpt p)
  -- fmap f p
  --   | isSimpleEnough p = OptSimple $ fmap f (unOpt p)
  --   | otherwise = OptOther $ fmap f (unOpt p)
  {-# INLINABLE fmap #-}

instance Grammar c g => Applicative (Opt c g) where
  pure = OptPure
  {-# INLINE pure #-}

  --  _ <*> _ | trace "<*>" False = undefined
  OptEmpty <*> _  = OptEmpty
  _ <*> OptEmpty  = OptEmpty
  OptPure f <*> g = fmap f g
  f <*> OptPure g = fmap ($ g) f
  f <*> g         = OptOther $ unOpt f <*> unOpt g
  {-# INLINABLE (<*>) #-}

instance (Defs g, Ord c, Enum c, Grammar c g) => Alternative (Opt c g) where
  empty = OptEmpty
  {-# INLINE empty #-}

  --  _ <|> _ | trace "<|>" False = undefined
  OptEmpty <|> e              = e
  OptSymb a <|> OptSymb b     = OptSymbI (RS.fromList [a, b])
  OptSymb a <|> OptSymbI bs   = OptSymbI (RS.insert a bs)
  OptSymbI as <|> OptSymb b   = OptSymbI (RS.insert b as)
  OptSymbI as <|> OptSymbI bs = OptSymbI (RS.union as bs)
  e <|> OptEmpty              = e
  g1 <|> g2                   = OptOther (unOpt g1 <|> unOpt g2)
  {-# INLINABLE (<|>) #-}

  many = Defs.manyD
  {-# INLINE many #-}

  some = Defs.someD
  {-# INLINE some #-}

instance FromSymb c (Opt c g) where
  symb = OptSymb
  {-# INLINE symb #-}
  symbI cs = if RS.null cs then OptEmpty else OptSymbI cs
  {-# INLINE symbI #-}

unOptRules :: (Defs g, Grammar c g) => D (Opt c g) as a -> D g as a
-- unOptRules _ | trace "unOptRules" False = undefined
unOptRules (OptRulesOther r)    = r
unOptRules (OptLifted p)        = liftD (unOpt p)
unOptRules (OptRulesCons p1 p2) = consD (unOpt p1) (unOptRules p2)

instance (Defs g, Grammar c g) => Defs (Opt c g) where
  data D (Opt c g) _as _a where
    OptRulesOther :: D g as a -> D (Opt c g) as a
    OptLifted     :: Opt c g a -> D (Opt c g) '[] a
    OptRulesCons  :: Opt c g a -> D (Opt c g) as b -> D (Opt c g) (a : as) b

  liftD = OptLifted
  {-# INLINE liftD #-}

  unliftD (OptLifted p)     = p
  unliftD (OptRulesOther r) = OptOther $ unliftD r
  {-# INLINE unliftD #-}

  consD = OptRulesCons
  {-# INLINE consD #-}

  letrD h = OptRulesOther $ letrD $ \a -> unOptRules $ h (OptOther a)
  -- letrDS h =
  --   -- FIXME: This tries to inline definitions, but we do not need to do it at this point, as unFlatten does so.
  --   case h (OptOther empty) of
  --     OptRulesCons (OptLifted res) _
  --       | isSimpleEnough res ->
  --         let ~(OptRulesCons _ r) = h res in r
  --     _ -> OptRulesOther $ letrDS $ \a -> unOptRules $ h (OptSimple a)

newtype ThawSpace g a = ThawSpace {runThawSpace :: g ExChar -> g ExChar -> g a}

instance Functor g => Functor (ThawSpace g) where
  fmap f x = ThawSpace $ \sp sps -> fmap f (runThawSpace x sp sps)
  {-# INLINE fmap #-}

instance Applicative g => Applicative (ThawSpace g) where
  pure a = ThawSpace $ \_ _ -> pure a
  {-# INLINE pure #-}

  f <*> g = ThawSpace $ \sp sps -> runThawSpace f sp sps <*> runThawSpace g sp sps
  {-# INLINE (<*>) #-}

instance (Defs g, Alternative g) => Alternative (ThawSpace g) where
  empty = ThawSpace $ \_ _ -> empty
  {-# INLINE empty #-}

  f <|> g = ThawSpace $ \sp sps -> runThawSpace f sp sps <|> runThawSpace g sp sps
  {-# INLINE (<|>) #-}

  many = Defs.manyD
  {-# INLINE many #-}
  some = Defs.someD
  {-# INLINE some #-}


instance (Alternative g, FromSymb Char g) => FromSymb ExChar (ThawSpace g) where
  symb Space          = ThawSpace $ \sp _ -> sp
  symb Spaces         = ThawSpace $ \_ sps -> sps
  symb (NormalChar c) = ThawSpace $ \_ _ -> NormalChar <$> symb c
  {-# INLINE symb #-}

  symbI cs = ThawSpace $ \sp sps ->
    let r1 = if RS.member Space cs then sp else empty
        r2 = if RS.member Spaces cs then sps else empty
        r3 =
          let rs = RS.toRangeList $ RS.delete Space $ RS.delete Spaces cs
           in fmap fromChar $
                symbI $
                  RS.fromNormalizedRangeList $ map (bimap unNormalChar unNormalChar) rs
     in r1 <|> r2 <|> r3
     where
       unNormalChar (NormalChar c) = c
       unNormalChar _              = error "Cannot happen."
  {-# INLINE symbI #-}

--  constantResult f a = ThawSpace $ \sp sps -> constantResult f (runThawSpace a sp sps)

instance Defs g => Defs (ThawSpace g) where
  newtype D (ThawSpace g) as a = ThawSpaces {runThawSpaces :: g ExChar -> g ExChar -> D g as a}

  liftD a = ThawSpaces $ \sp sps -> liftD (runThawSpace a sp sps)
  {-# INLINE liftD #-}

  unliftD a = ThawSpace $ \sp sps -> unliftD (runThawSpaces a sp sps)
  {-# INLINE unliftD #-}

  consD x y = ThawSpaces $ \sp sps -> consD (runThawSpace x sp sps) (runThawSpaces y sp sps)
  {-# INLINE consD #-}

  letrD k = ThawSpaces $ \sp sps ->
    letrD $ \a -> runThawSpaces (k $ ThawSpace $ \_ _ -> a) sp sps
  {-# INLINE letrD #-}

thawSpace :: (Defs exp, Alternative exp) => exp () -> ThawSpace exp a -> exp a
thawSpace sp0 g = local $ do
  sp  <- share (Space <$ sp0)
  sps <- share (Spaces <$ many sp)
  return (runThawSpace g sp sps)
{-# INLINE thawSpace #-}

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
      _                                -> f q1' q2' x'

data Qsp = Qn | Qs | Qss deriving stock (Eq, Ord)

optSpaces :: forall g t. (Defs g, Grammar ExChar g) => FlatGrammar ExChar t -> g t
optSpaces (FlatGrammar (defs :: Bindings inc env env) rhs0) =
  local $ evalStateT (asum <$> mapM (\qf -> (<* finalProd qf) <$> procRHS Qn qf rhs0) allStates) emptyMemo
  where
    allStates = [Qn, Qs, Qss]

    finalProd Qn  = pure ()
    finalProd Qs  = void (symb Space)
    finalProd Qss = void (symb Spaces)
    {-# INLINE finalProd #-}

    transTo Qn Space           = (pure Space, Qs)
    transTo Qn Spaces          = (pure Spaces, Qss)
    transTo Qn (NormalChar c)  = (char c, Qn)
    transTo Qs Space           = (symb Space, Qs)
    transTo Qs Spaces          = (symb Space, Qss)
    transTo Qs (NormalChar c)  = (symb Space *> char c, Qn)
    transTo Qss Space          = (symb Space, Qss)
    transTo Qss Spaces         = (pure Spaces, Qss)
    transTo Qss (NormalChar c) = (symb Spaces *> char c, Qn)
    {-# INLINE transTo #-}

    procRHS :: Qsp -> Qsp -> RHS inc env a -> StateT (Memo env g) (DefM g) (g a)
    procRHS q1 q2 (RHS ps) = asum <$> mapM (procProd q1 q2) ps

    procProd :: Qsp -> Qsp -> Prod inc env a -> StateT (Memo env g) (DefM g) (g a)
    procProd q1 q2 (PNil a)
      | q1 == q2  = return (pure a)
      | otherwise = return empty
    procProd q1 q2 (PCons (SymbI cs) r) = do
      r1 <- if RS.member Space cs  then procProd q1 q2 (PCons (Symb Space) r)  else pure empty
      r2 <- if RS.member Spaces cs then procProd q1 q2 (PCons (Symb Spaces) r) else pure empty
      r3 <- do
        let cs' = RS.delete Space $ RS.delete Spaces cs
        let o = case q1 of
              Qn  -> symbI cs'
              Qs  -> symb Space *> symbI cs'
              Qss -> symb Spaces *> symbI cs'
        rr <- procProd Qn q2 r
        return $ (\a f -> f a) <$> o <*> rr
      return (r1 <|> r2 <|> r3)

    procProd q1 q2 (PCons (Symb c) r) = do
      let (os, qm) = transTo q1 c
      g <- procProd qm q2 r
      return $ (\a k -> k a) <$> os <*> g
    procProd q1 q2 (PCons (NT x) r) =
      fmap asum $
        forM allStates $ \qm -> do
          g1 <- procVar q1 qm x
          g2 <- procProd qm q2 r
          return $ (\a k -> k a) <$> g1 <*> g2

    procVar :: Qsp -> Qsp -> Var env a -> StateT (Memo env g) (DefM g) (g a)
    procVar q1 q2 x = StateT $ \memo ->
      case lookupMemo memo q1 q2 x of
        Just r -> return (r, memo)
        Nothing -> do
          let rhs = E.lookupEnv x defs
          letr1 $ \a -> do
            (r, memo') <- runStateT (procRHS q1 q2 rhs) (updateMemo memo q1 q2 x a)
            return (r, (a, memo'))


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
collapseSpace = optSpaces
{-# INLINE collapseSpace #-}

-- | Thawing 'Space' and 'Spaces'.
withSpace :: (Defs exp, Grammar Char exp) => exp () -> SemToFlatGrammar ExChar a -> exp a
withSpace gsp g = thawSpace gsp $ simplifyGrammar $ collapseSpace (flatten g)
{-# INLINE withSpace #-}
