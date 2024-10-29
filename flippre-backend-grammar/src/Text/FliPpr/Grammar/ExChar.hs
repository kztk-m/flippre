{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Text.FliPpr.Grammar.ExChar (
  -- * Basic Manipulation
  ExChar (..),
  CharLike (..),
  char,
  text,
  space,
  spaces,

  -- * Conversion of CFGs involving ExChar
  withSpace,
) where

import Control.Applicative (Alternative (..), asum)
import Control.Monad (forM, void)
import Data.Bifunctor (bimap)
import qualified Data.RangeSet.List as RS
import Data.String (IsString (..))

import qualified Prettyprinter as PP

import Control.Monad.State (StateT (..), evalStateT)
import Data.Typeable ((:~:) (..))
import Defs
import Text.FliPpr.Grammar.Flatten (flatten)
import Text.FliPpr.Grammar.Internal.Util
import Text.FliPpr.Grammar.Simplify (simplify)
import Text.FliPpr.Grammar.Types

-- | Characters with special symbols 'Space' and 'Spaces'. They will be
--   converted to a single "white space" and zero-or-more "white spaces", by
--   'withSpace' so that concatenation of 'Space' and 'Spaces' does not lead to
--   ambiguity. The "white space" here is not necessarily the space character,
--   'withSpace' provides users to specify how "white spaces" are interpreted.
data ExChar
  = -- | Special symbol denoting a single space " "
    Space
  | -- | Special symbol denoting zero-or-more spaces
    Spaces
  | -- | Normal charactors (which may be " ")
    NormalChar {-# UNPACK #-} !Char
  deriving stock (Eq, Ord)

instance PP.Pretty ExChar where
  pretty (NormalChar c) = PP.squotes (PP.pretty c)
  pretty Space = fromString "_"
  pretty Spaces = fromString "_*"

  prettyList = uncurry pprList' . chars []
    where
      chars s (NormalChar c : cs) = chars (c : s) cs
      chars s r = (reverse s, r)

      pprList' [] [] = fromString ""
      pprList' [] (c : cs) = case cs of [] -> PP.pretty c; _ -> PP.pretty c PP.<+> PP.prettyList cs
      pprList' s [] = PP.pretty s
      pprList' s r = PP.pretty s PP.<+> PP.prettyList r

instance Show ExChar where
  show = show . PP.pretty
  showList s r = show (PP.prettyList s) ++ r

instance Enum ExChar where
  toEnum 0 = Space
  toEnum 1 = Spaces
  toEnum n = NormalChar (toEnum $! n - 2)

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
space :: (Grammar ExChar e) => e ()
space = void (symb Space)

-- | A production of the special symbol 'Spaces'
spaces :: (Grammar ExChar e) => e ()
spaces = void (symb Spaces)

newtype ThawSpace g a = ThawSpace {runThawSpace :: g ExChar -> g ExChar -> g a}

instance (Functor g) => Functor (ThawSpace g) where
  fmap f x = ThawSpace $ \sp sps -> fmap f (runThawSpace x sp sps)
  {-# INLINE fmap #-}

instance (Applicative g) => Applicative (ThawSpace g) where
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
  symb Space = ThawSpace $ \sp _ -> sp
  symb Spaces = ThawSpace $ \_ sps -> sps
  symb (NormalChar c) = ThawSpace $ \_ _ -> NormalChar <$> symb c
  {-# INLINE symb #-}

  symbI cs = ThawSpace $ \sp sps ->
    let r1 = if RS.member Space cs then sp else empty
        r2 = if RS.member Spaces cs then sps else empty
        r3 =
          let rs = RS.toRangeList $ RS.delete Space $ RS.delete Spaces cs
          in  fmap fromChar $
                symbI $
                  RS.fromNormalizedRangeList $
                    map (bimap unNormalChar unNormalChar) rs
    in  r1 <|> r2 <|> r3
    where
      unNormalChar (NormalChar c) = c
      unNormalChar _ = error "Cannot happen."
  {-# INLINE symbI #-}

--  constantResult f a = ThawSpace $ \sp sps -> constantResult f (runThawSpace a sp sps)

instance (Defs g) => Defs (ThawSpace g) where
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
  sp <- share (Space <$ sp0)
  sps <- share (Spaces <$ many sp)
  return (runThawSpace g sp sps)
{-# INLINE thawSpace #-}

-- FIXME: will be replaced by Map2
newtype Memo env g = Memo {lookupMemo :: forall a. Qsp -> Qsp -> Ix env a -> Maybe (g a)}

emptyMemo :: Memo env g
emptyMemo = Memo $ \_ _ _ -> Nothing

updateMemo :: Memo env g -> Qsp -> Qsp -> Ix env a -> g a -> Memo env g
updateMemo (Memo f) q1 q2 x k =
  Memo $ \q1' q2' x' ->
    case eqIx x x' of
      Just Refl | q1 == q1', q2 == q2' -> Just k
      _ -> f q1' q2' x'

data Qsp = Qn | Qs | Qss deriving stock (Eq, Ord)

optSpaces :: forall g t. (Defs g, Grammar ExChar g) => FlatGrammar ExChar t -> g t
optSpaces (FlatGrammar (defs :: Env (RHS inc env) env) rhs0) =
  local $ evalStateT (asum <$> mapM (\qf -> (<* finalProd qf) <$> procRHS Qn qf rhs0) allStates) emptyMemo
  where
    allStates = [Qn, Qs, Qss]

    finalProd Qn = pure ()
    finalProd Qs = void (symb Space)
    finalProd Qss = void (symb Spaces)
    {-# INLINE finalProd #-}

    transTo Qn Space = (pure Space, Qs)
    transTo Qn Spaces = (pure Spaces, Qss)
    transTo Qn (NormalChar c) = (char c, Qn)
    transTo Qs Space = (symb Space, Qs)
    transTo Qs Spaces = (symb Space, Qss)
    transTo Qs (NormalChar c) = (symb Space *> char c, Qn)
    transTo Qss Space = (symb Space, Qss)
    transTo Qss Spaces = (pure Spaces, Qss)
    transTo Qss (NormalChar c) = (symb Spaces *> char c, Qn)
    {-# INLINE transTo #-}

    procRHS :: Qsp -> Qsp -> RHS inc env a -> StateT (Memo env g) (DefM g) (g a)
    procRHS q1 q2 (MkRHS ps) = asum <$> mapM (procProd q1 q2) ps

    procProd :: Qsp -> Qsp -> Prod inc env a -> StateT (Memo env g) (DefM g) (g a)
    procProd q1 q2 (PNil a)
      | q1 == q2 = return (pure a)
      | otherwise = return empty
    procProd q1 q2 (PCons (SymbI cs) r) = do
      r1 <- if RS.member Space cs then procProd q1 q2 (PCons (Symb Space) r) else pure empty
      r2 <- if RS.member Spaces cs then procProd q1 q2 (PCons (Symb Spaces) r) else pure empty
      r3 <- do
        let cs' = RS.delete Space $ RS.delete Spaces cs
        let o = case q1 of
              Qn -> symbI cs'
              Qs -> symb Space *> symbI cs'
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

    procVar :: Qsp -> Qsp -> Ix env a -> StateT (Memo env g) (DefM g) (g a)
    procVar q1 q2 x = StateT $ \memo ->
      case lookupMemo memo q1 q2 x of
        Just r -> return (r, memo)
        Nothing -> do
          let rhs = lookEnv defs x
          letr1 $ \a -> do
            (r, memo') <- runStateT (procRHS q1 q2 rhs) (updateMemo memo q1 q2 x a)
            return (r, (a, memo'))

collapseSpace :: (Defs g, Grammar ExChar g) => FlatGrammar ExChar a -> g a
collapseSpace = optSpaces
{-# INLINE collapseSpace #-}

-- | Thawing 'Space' and 'Spaces'.
withSpace :: (Defs exp, Grammar Char exp) => exp () -> (forall f. (GrammarD ExChar f) => f a) -> exp a
withSpace gsp g = thawSpace gsp $ simplify $ collapseSpace (flatten g)
{-# INLINE withSpace #-}