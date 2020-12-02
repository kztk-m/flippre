{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Text.FliPpr.Driver.Earley (EarleyProd, asEarley, parse) where

import Control.Applicative as A (Alternative (..))
-- import Text.FliPpr.Internal.GrammarST as G
-- import Text.FliPpr.Internal.Ref

-- import Control.Monad.Reader
-- import Data.Container2
-- import Data.Coerce (coerce)
-- import qualified Data.Map2 as M2
-- import Data.Maybe (fromJust)
import qualified Data.RangeSet.List as RS
import qualified Text.Earley as E
import Text.FliPpr.Doc as D
import Text.FliPpr.Err
import qualified Text.FliPpr.Grammar as G
import Text.FliPpr.Internal.Defs as Defs

newtype EarleyProd r c a = EarleyProd (E.Grammar r (E.Prod r c c a))

instance Functor (EarleyProd r c) where
  fmap f (EarleyProd e) = EarleyProd $ fmap (fmap f) e

instance Applicative (EarleyProd r c) where
  pure a = EarleyProd $ pure $ pure a
  EarleyProd f <*> EarleyProd a = EarleyProd $ (<*>) <$> f <*> a

instance Alternative (EarleyProd r c) where
  empty = EarleyProd $ return A.empty
  EarleyProd f <|> EarleyProd g = EarleyProd $ (<|>) <$> f <*> g

  many = Defs.manyD
  some = Defs.someD

instance Ord c => G.Grammar c (EarleyProd r c) where
  symb = EarleyProd . pure . E.namedToken
  symbI cs = EarleyProd $ pure $ E.satisfy (`RS.member` cs)

instance G.Defs (EarleyProd r c) where
  newtype Fs (EarleyProd r c) a = EarleyG {unEarleyG :: E.Grammar r (Defs.DTypeVal (EarleyProd r c) a)}

  liftDS e = EarleyG $ pure $ VT e
  unliftDS (EarleyG m) = EarleyProd $ do
    res <- m
    case res of
      VT (EarleyProd r) -> r

  pairDS (EarleyG m1) (EarleyG m2) = EarleyG $ VProd <$> m1 <*> m2

  -- unpairRules (EarleyG m) k = EarleyG $ do
  --   res <- m
  --   case res of
  --     VProd v1 v2 -> unEarleyG $ k (EarleyG $ return v1) (EarleyG $ return v2)

  letrDS f = EarleyG $ do
    rec (a, r) <- do
          res <- unEarleyG $ f a
          return $ case res of
            VProd (VT b) r -> (b, r)
    return r

asEarley :: EarleyProd r c t -> E.Grammar r (E.Prod r c c t)
asEarley (EarleyProd m) = m

parse :: (Show c, Ord c) => (forall g. G.GrammarD c g => g (Err a)) -> [c] -> Err [a]
parse g str =
  case E.fullParses (E.parser (asEarley g)) str of
    (as@(_ : _), _) -> sequence as
    ([], E.Report i es v) ->
      err $
        D.hsep
          [ D.text "Error: parse error",
            D.align $
              D.vsep
                [ D.text "at position" <+> ppr i,
                  D.text "expecting:" <+> D.text (show es),
                  D.text "near:" <+> D.text (show v)
                ]
          ]

-- type GatherM s c
--   = ReaderT
--     (RawRef s (M2.Map2 (RefK s (RHS s c)) (RHS s c)))
--     (RefM s)

-- type PTable s c r
--   = M2.Map2 (RefK s (RHS s c)) (E.Prod r [c] c)

-- data Earley = Earley

-- instance Driver Earley where
--   parse _ = parseEarley

-- parseEarley :: (Pretty c, Ord c) => G.Grammar c (Err a) -> [c] -> Err [a]
-- parseEarley g str =
--   case E.fullParses (E.parser (convert g)) str of
--     (as@(_:_),_)               -> sequence as
--     ([],E.Report i es v) ->
--       err $ D.text "Error: parse error"
--          D.<+> D.align (D.text "at position"  <+> ppr i </>
--                         D.text "expecting:"   <+> ppr es </>
--                         D.text "near:"        <+> ppr v)

-- convert :: (Ord c) => G.Grammar c a -> E.Grammar r (E.Prod r [c] c a)
-- convert (G.Grammar s) = runRefM $ do
--   ref <- s
--   tbRef <- newRawRef $ M2.empty
--   runReaderT (gatherSymb (NT ref)) tbRef
--   tb <- readRawRef tbRef
--   return $ makeGrammar ref tb
--     where
--       gatherSymb :: (Ord c) => G.Symb G.RHS s c a -> GatherM s c ()
--       gatherSymb (Term _) = return ()
--       gatherSymb (TermI _) = return ()
--       gatherSymb (NT r) = do
--         tbRef <- ask
--         tb <- readRawRef tbRef
--         case M2.lookup (RefK r) tb of
--           Just _ -> return ()
--           Nothing  -> do
--             rhs <- readRef r
--             modifyRawRef tbRef (M2.insert (coerce r) rhs)
--             gatherRHS rhs

--       gatherRHS :: Ord c => G.RHS s c a -> GatherM s c ()
--       gatherRHS (RHS rs) = mapM_ gatherProd rs

--       gatherProd :: Ord c => G.Prod s c a -> GatherM s c ()
--       gatherProd (PNil _) = return ()
--       gatherProd (PCons r s) = gatherSymb r >> gatherProd s

--       makeGrammar :: Ord c => Ref s (RHS s c a) -> M2.Map2 (RefK s (RHS s c)) (RHS s c) -> E.Grammar r (E.Prod r [c] c a)
--       makeGrammar ref table = do
--         rec ptable <- traverse2 (E.rule . goRHS ptable) table
--         return $ fromJust $ M2.lookup (coerce ref) ptable
--           where
--             goRHS :: Ord c => PTable s c r -> G.RHS s c a -> E.Prod r [c] c a
--             goRHS ptable (RHS rs) = foldr (<|>) A.empty $ map (goProd ptable) rs

--             goProd :: Ord c => PTable s c r -> G.Prod s c a -> E.Prod r [c] c a
--             goProd _      (PNil f) = pure f
--             goProd ptable (PCons s r) =
--               fmap (\a k -> k a) (goSymb ptable s) <*> goProd ptable r

--             goSymb :: Ord c => PTable s c r -> G.Symb G.RHS s c a -> E.Prod r [c] c a
--             goSymb _      (Term c)   = E.token c
--             goSymb _      (TermI cs) = E.satisfy (\c -> RS.member c cs)
--             goSymb ptable (NT x)     = fromJust $ M2.lookup (coerce x) ptable
