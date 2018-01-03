{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE GADTs #-}

module Text.FliPpr.Driver.Earley where

import qualified Text.Earley as E
import qualified Data.Map2 as M2
import Control.Applicative as A (Alternative(..)) 

import Text.FliPpr.Internal.GrammarST as G
import Text.FliPpr.Internal.Ref
import Text.FliPpr.Err 

import Text.FliPpr.Doc as D 

import Control.Monad.Reader
import Data.Maybe (fromJust)

import Data.Container2 
import Data.Coerce 

type GatherM s c
  = ReaderT
    (RawRef s (M2.Map2 (RefK s (RHS s c)) (RHS s c)))
    (RefM s)

type PTable s c r
  = M2.Map2 (RefK s (RHS s c)) (E.Prod r [c] c)

data Earley = Earley

instance Driver Earley where
  parse _ = parseEarley

parseEarley :: (Pretty c, Eq c) => G.Grammar c (Err a) -> [c] -> Err [a]
parseEarley g str =
  case E.fullParses (E.parser (convert g)) str of
    (as@(_:_),_)               -> sequence as
    ([],E.Report i es v) ->
      err $ D.text "Error: parse error"
         D.<+> D.align (D.text "at position"  <+> ppr i </>
                        D.text "expecting:"   <+> ppr es </>
                        D.text "near:"        <+> ppr v)

convert :: Eq c => G.Grammar c a -> E.Grammar r (E.Prod r [c] c a)
convert (G.Grammar s) = runRefM $ do
  ref <- s 
  tbRef <- newRawRef $ M2.empty
  runReaderT (gatherSymb (NT ref)) tbRef
  tb <- readRawRef tbRef
  return $ makeGrammar ref tb 
    where
      gatherSymb :: Eq c => G.Symb G.RHS s c a -> GatherM s c ()
      gatherSymb (Term _) = return ()
      gatherSymb (NT r) = do
        tbRef <- ask
        tb <- readRawRef tbRef
        case M2.lookup (RefK r) tb of
          Just _ -> return () 
          Nothing  -> do
            rhs <- readRef r
            modifyRawRef tbRef (M2.insert (coerce r) rhs)
            gatherRHS rhs

      gatherRHS :: Eq c => G.RHS s c a -> GatherM s c ()
      gatherRHS (RHS rs) = mapM_ gatherProd rs  

      gatherProd :: Eq c => G.Prod s c a -> GatherM s c () 
      gatherProd (PNil _) = return ()
      gatherProd (PCons r s) = gatherSymb r >> gatherProd s 
      
      makeGrammar :: Eq c => Ref s (RHS s c a) -> M2.Map2 (RefK s (RHS s c)) (RHS s c) -> E.Grammar r (E.Prod r [c] c a)
      makeGrammar ref table = do 
        rec ptable <- traverse2 (E.rule . goRHS ptable) table
        return $ fromJust $ M2.lookup (coerce ref) ptable
          where
            goRHS :: Eq c => PTable s c r -> G.RHS s c a -> E.Prod r [c] c a
            goRHS ptable (RHS rs) = foldr (<|>) A.empty $ map (goProd ptable) rs

            goProd :: Eq c => PTable s c r -> G.Prod s c a -> E.Prod r [c] c a
            goProd _      (PNil f) = pure f
            goProd ptable (PCons s r) =
              fmap (\a k -> k a) (goSymb ptable s) <*> goProd ptable r 

            goSymb :: Eq c => PTable s c r -> G.Symb G.RHS s c a -> E.Prod r [c] c a
            goSymb _      (Term c) = E.token c
            goSymb ptable (NT x)   = fromJust $ M2.lookup (coerce x) ptable
  


  
