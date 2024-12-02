{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Text.FliPpr.Grammar.Simplify (simplify) where

import Control.Applicative (Alternative (..), Const (..))
import Data.Maybe (mapMaybe)
import Data.Monoid (Endo (..))
import Data.RangeSet.List (RSet)
import qualified Data.RangeSet.List as RS
import Defs
import Text.FliPpr.Grammar.Flatten (flatten)
import Text.FliPpr.Grammar.Internal.Util
import Text.FliPpr.Grammar.Types
import Text.FliPpr.Grammar.UnFlatten (unFlatten)

removeNonProductive :: FlatGrammar c a -> FlatGrammar c a
removeNonProductive (FlatGrammar (defs :: Env (RHS c env0) env0) rhs) =
  -- trace (show $ fromString " " D.<> D.align (D.pretty $ FlatGrammar defs rhs)) $
  FlatGrammar (mapEnv procRHS defs) (procRHS rhs)
  where
    prodTable = check initTable

    initTable = mapEnv (const $ Const False) defs

    checkRHS :: Env (Const Bool) env' -> RHS c env' a -> Bool
    checkRHS env (MkRHS rs) = any (checkProd env) rs

    checkProd :: Env (Const Bool) env' -> Prod c env' a -> Bool
    checkProd _ (PNil _) = True
    checkProd env (PCons s r) = checkSymb env s && checkProd env r

    checkSymb :: Env (Const Bool) env' -> Symb c env' a -> Bool
    checkSymb _ (Symb _) = True
    checkSymb _ (SymbI cs) = not (RS.null cs)
    checkSymb env (NT x) = getConst $ lookEnv env x

    checkDefs :: Env (RHS c env') env -> Env (Const Bool) env' -> Env (Const Bool) env
    checkDefs es env = mapEnv (Const . checkRHS env) es

    -- pprMP mp = E.pprEnv (\s d -> D.hsep [fromString s, fromString "=", fromString (show $ getConst d)]) mp :: D.Doc

    check mp =
      let mp' = checkDefs defs mp
          flag = appEndo (getConst $ zipWithEnvA (\(Const b1) (Const b2) -> Const $ Endo (\x -> x || (b1 /= b2))) mp mp') False
      in  -- trace (show $ fromString "  " D.<> D.align (pprMP mp D.</> pprMP mp' D.</> fromString "flag: " D.<> fromString (show flag))) $
          if flag then check mp' else mp'

    procRHS :: RHS c env0 a -> RHS c env0 a
    procRHS (MkRHS rs) = MkRHS $ mapMaybe procProd rs

    procProd :: Prod c env0 a -> Maybe (Prod c env0 a)
    procProd (PNil a) = return (PNil a)
    procProd (PCons s r) = PCons <$> procSymb s <*> procProd r

    procSymb :: Symb c env0 a -> Maybe (Symb c env0 a)
    procSymb (Symb c) = return (Symb c)
    procSymb (SymbI cs) = if RS.null cs then Nothing else return (SymbI cs)
    procSymb (NT x) = if getConst (lookEnv prodTable x) then return (NT x) else Nothing

-- | a simple optimizing interpretation
-- We use the property that
--
--   symb a <|> symb b = symbI (RS.singleton a `RS.union` RS.singleton b)
data Opt c g a where
  OptSymb :: !c -> Opt c g c
  OptSymbI :: !(RSet c) -> Opt c g c
  OptEmpty :: Opt c g a
  OptPure :: a -> Opt c g a
  -- OptSimple :: g a -> Opt c g a -- inlinable
  OptOther :: !(g a) -> Opt c g a

-- | Simplification of grammars, it performs:
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
simplify :: (Ord c, Enum c, GrammarD c g) => (forall h. (GrammarD c h) => h a) -> g a
simplify g = unOpt $ unFlatten $ removeNonProductive $ flatten $ unOpt g

unOpt :: (Grammar c g) => Opt c g a -> g a
unOpt (OptSymb c) = symb c
unOpt (OptSymbI cs) = symbI cs
unOpt OptEmpty = empty
unOpt (OptPure a) = pure a
-- unOpt (OptSimple p) = p
unOpt (OptOther p) = p

-- isSimpleEnough :: Opt c g a -> Bool
-- isSimpleEnough (OptOther _) = False
-- isSimpleEnough _            = True

instance (Grammar c g) => Functor (Opt c g) where
  fmap f (OptPure a) = OptPure (f a)
  fmap _ OptEmpty = OptEmpty
  fmap f p = OptOther $ fmap f (unOpt p)
  -- fmap f p
  --   | isSimpleEnough p = OptSimple $ fmap f (unOpt p)
  --   | otherwise = OptOther $ fmap f (unOpt p)
  {-# INLINEABLE fmap #-}

instance (Grammar c g) => Applicative (Opt c g) where
  pure = OptPure
  {-# INLINE pure #-}

  --  _ <*> _ | trace "<*>" False = undefined
  OptEmpty <*> _ = OptEmpty
  _ <*> OptEmpty = OptEmpty
  OptPure f <*> g = fmap f g
  f <*> OptPure g = fmap ($ g) f
  f <*> g = OptOther $ unOpt f <*> unOpt g
  {-# INLINEABLE (<*>) #-}

instance (Defs g, Ord c, Enum c, Grammar c g) => Alternative (Opt c g) where
  empty = OptEmpty
  {-# INLINE empty #-}

  --  _ <|> _ | trace "<|>" False = undefined
  OptEmpty <|> e = e
  OptSymb a <|> OptSymb b = OptSymbI (RS.fromList [a, b])
  OptSymb a <|> OptSymbI bs = OptSymbI (RS.insert a bs)
  OptSymbI as <|> OptSymb b = OptSymbI (RS.insert b as)
  OptSymbI as <|> OptSymbI bs = OptSymbI (RS.union as bs)
  e <|> OptEmpty = e
  g1 <|> g2 = OptOther (unOpt g1 <|> unOpt g2)
  {-# INLINEABLE (<|>) #-}

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
unOptRules (OptRulesOther r) = r
unOptRules (OptLifted p) = liftD (unOpt p)
unOptRules (OptRulesCons p1 p2) = consD (unOpt p1) (unOptRules p2)

instance (Defs g, Grammar c g) => Defs (Opt c g) where
  data D (Opt c g) _as _a where
    OptRulesOther :: D g as a -> D (Opt c g) as a
    OptLifted :: Opt c g a -> D (Opt c g) '[] a
    OptRulesCons :: Opt c g a -> D (Opt c g) as b -> D (Opt c g) (a : as) b

  liftD = OptLifted
  {-# INLINE liftD #-}

  unliftD (OptLifted p) = p
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