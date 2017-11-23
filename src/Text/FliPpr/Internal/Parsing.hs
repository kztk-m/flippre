{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE GADTs #-}
module Text.FliPpr.Internal.Parsing where

import Text.FliPpr.Internal.Type
import Control.Monad.Fix (MonadFix(..))
import Control.Monad (void)
import Control.Monad.Writer hiding ((<>))
import Control.Monad.State 

import qualified Data.IntMap as IM 

import Control.Applicative
import Control.Arrow (first, second)
import Data.Char

import Control.Monad.ST
import Data.STRef 

import Data.Kind 

import Data.Coerce

import Text.FliPpr.Doc as D hiding (empty) 
import qualified Text.FliPpr.Doc as D 

import Debug.Trace

class (Applicative p, Alternative p) => ParserLike p where
  pchar :: Char -> p Char
  pchar c = psatisfy (== c)
                       
  psatisfy :: (Char -> Bool) -> p Char 

  ptext :: String -> p String
  ptext []     = pure []
  ptext (c:cs) = (:) <$> pchar c <*> ptext cs 

  pfail :: String -> p a 

  -- for efficient manipulalation
  pspaces :: p () 
  -- pspaces = pfix (\x -> void (ptext "") <|> (space *> x))
  --   where
  --     space = psatisfy (isSpace)

class ParserLike p => ParserFix p where
  -- Is it really useful? 
  pfix  :: (p a -> p a) -> p a 
  

class (ParserLike p, MonadFix m) => Grammar m p where
  prule :: p a -> m (p a) 


-- an interpretation to replace pfix by prule.
newtype LiftRec m p a = LiftRec { unLiftRec :: m (p a) }

instance (Functor m, Functor p) => Functor (LiftRec m p) where
  fmap f (LiftRec m) = LiftRec (fmap (fmap f) m)

instance (Applicative m, Applicative p) => Applicative (LiftRec m p) where
  pure = LiftRec . pure . pure
  LiftRec mf <*> LiftRec ma =
    LiftRec $ liftA2 (<*>) mf ma  

instance (Applicative m, Alternative p) => Alternative (LiftRec m p) where
  empty = LiftRec (pure empty)
  LiftRec ma <|> LiftRec mb =
    LiftRec $ liftA2 (<|>) ma mb

instance (Applicative m, ParserLike p) => ParserLike (LiftRec m p) where
  pchar c    = LiftRec (pure (pchar c))
  psatisfy q = LiftRec (pure (psatisfy q))
  pfail s    = LiftRec (pure (pfail s))

  ptext s    = LiftRec (pure (ptext s))
  
  pspaces    = LiftRec (pure pspaces)


instance Grammar m p => ParserFix (LiftRec m p) where
  pfix f = LiftRec $ do
    let k a = let LiftRec m = f (LiftRec (return a))
              in m >>= prule
    mfix k

instance Grammar m p => Grammar m (LiftRec m p) where
  prule (LiftRec m) = fmap (LiftRec . prule) m


liftFix :: (forall p. (ParserFix p, Grammar m p) => p a) ->
           (forall p. (ParserLike p, Grammar m p) => m (p a))
liftFix m =
  case m of
    LiftRec x -> x 


-- data Par (v :: Type -> Type) :: Type -> Type where     
--   PText   :: String -> Par v a
--   PSeq    :: Par v (a -> b) -> Par v a -> Par v b
--   PChoice :: Par v a -> Par v a -> Par v a
--   PFix    :: (v a -> Par v a) -> Par v a
--   PVar    :: v a -> Par v a
--   PPure   :: a -> Par v a
--   PSpaces :: Par v String 


{-
prule :: Par v a -> m (Par v a)


-}

-- interp :: ParserFix p => Par p a -> p a
-- interp (PVar x) = x
-- interp (PFix f) = pfix (\x -> interp (f x))
-- -- ....

-- newtype Mu v a = Mu { unMu :: v (Mu v) a } 

-- instance Functor (Par (Mu Par)) where
--   fmap f a = pure f <*> a 

-- instance Applicative (Par (Mu Par)) where
--   pure  = PPure
--   (<*>) = PSeq

-- instance Alternative (Par (Mu Par)) where 
  
  
-- instance ParserLike (Par (Mu Par)) where


-- instance ParserFix (Par (Mu Par)) where
--   pfix f = PFix (\x -> f (unMu x))



  
{-

data Delay p a = Delay (Maybe ID) Delay
               | App2 (p s -> p t -> p a) (Delay p s) (Delay p t)
               | App  (p s -> p a) (Delay p s)

-- delay forms a monad

prule p = do
  i <- newID
  return $ Delay (Just i) (Now p)

instance ParserLike Delay p where 
  ptext s = Now (ptext s)

instance Applicative Delay p where 
  pure a = Now (pure a)
  Now f     <*> Now a     = Now (f a)
  Now f     <*> Delay i d = Delay Nothing (Now a <*> d)
  Delay _ f <*> a         = Delay Nothing (f a)

instance Alternative Delay p where
  empty = Now empty
  Now a <|> Now b = Now (a <|> b)
  ...

resolve :: Delay p a -> (ID -> p a) -> p a
resolve def = go [] (Delay p a)
  where
    go vs (Delay (Just k) d)
      | k `elem` vs = def k 
      | _           = go (k : vs) d
   go vs (Delay Nothing d) = go vs d
   go vs (Now a) = a

-}
                                




-- data NormSPContext = CSpaces | CNormal     
-- newtype NormSP p a = NormSP { unNormSP :: State NormSPContext (p a) }

-- instance Functor p => Functor (NormSP p) where
--   fmap f = NormSP . fmap (fmap f) . unNormSP

-- instance Applicative p => Applicative (NormSP p) where
--   pure = NormSP . pure . pure
--   NormSP mf <*> NormSP ma = NormSP (liftA2 (<*>) mf ma)

-- instance Alternative p => Alternative (NormSP p) where
--   empty = NormSP (pure empty)
--   NormSP ma <|> NormSP mb = NormSP (liftA2 (<|>) ma mb)


-- instance ParserLike p => ParserLike (NormSP p) where
--   psatisfy p = NormSP $ do
--     put CNormal
--     return $ psatisfy p

--   pchar p = NormSP $ put CNormal >> return (pchar p)
--   pfail s = NormSP (return (pfail s))
--   pspaces = NormSP $ do
--     c <- get
--     case c of
--       CSpaces ->
--         return (pure ())
--       _ ->
--         put CSpaces >> return pspaces

data NormSP p a = NormSP { normSPss :: (p a) -- parser that occurs after spaces, ends with spaces
                         , normSPsn :: (p a) -- parser that occurs after spaces, ends without spaces
                         , normSPns :: (p a) -- parser that does not occur after spaces, ends with spaces
                         , normSPnn :: (p a) } -- parser that does not occur after spaces, ends without spaces
                  
instance Functor p => Functor (NormSP p) where
  fmap f (NormSP p1 p2 p3 p4) = NormSP (fmap f p1) (fmap f p2) (fmap f p3) (fmap f p4)

instance Alternative p => Applicative (NormSP p) where
  pure a = NormSP (pure a) empty empty (pure a)
  p1 <*> p2 =
    NormSP { normSPss = normSPss p1 <*> normSPss p2 
                        <|> normSPsn p1 <*> normSPns p2
           , normSPsn = normSPss p1 <*> normSPsn p2
                        <|> normSPsn p1 <*> normSPnn p2
           , normSPns = normSPns p1 <*> normSPss p2
                        <|> normSPnn p1 <*> normSPns p2
           , normSPnn = normSPns p1 <*> normSPsn p2
                        <|> normSPnn p1 <*> normSPnn p2 }

instance Alternative p => Alternative (NormSP p) where
  empty = NormSP empty empty empty empty
  p1 <|> p2 =
    NormSP { normSPss = normSPss p1 <|> normSPss p2
           , normSPsn = normSPsn p1 <|> normSPsn p2
           , normSPns = normSPns p1 <|> normSPns p2
           , normSPnn = normSPnn p1 <|> normSPnn p2 } 

instance ParserLike p => ParserLike (NormSP p) where
  psatisfy q =
    NormSP { normSPss = empty
           , normSPsn = psatisfy q
           , normSPns = empty
           , normSPnn = psatisfy q }
  pchar c    =
    NormSP { normSPss = empty
           , normSPsn = pchar c
           , normSPns = empty
           , normSPnn = pchar c }

  ptext []   = pure [] 
  ptext s    =
    NormSP { normSPss = empty
           , normSPsn = ptext s
           , normSPns = empty
           , normSPnn = ptext s }

  pfail s    = NormSP (pfail s) (pfail s) (pfail s) (pfail s)
  
  pspaces    =
    NormSP { normSPss = pure ()
           , normSPsn = empty
           , normSPns = pspaces 
           , normSPnn = empty } 

-- pfix2 :: ParserFix p => ((p a, p b) -> (p a, p b)) -> (p a, p b)
-- pfix2 f = (pfix (\a -> fst (f (a, pfix (\b -> snd (f (a, b)))))),
--            pfix (\b -> snd (f (pfix (\a -> fst (f (a, b))), b))))
          

instance ParserFix p => ParserFix (NormSP p) where
  pfix f = let ((s,t),(v,w)) =
                 pfix4 (\((a,b),(c,d)) -> let NormSP a' b' c' d' = f (NormSP a b c d)
                                          in ((a',b'),(c',d')))
           in NormSP s t v w 
    where
      pfix2 :: ((b -> b) -> b) -> ((b,b) -> (b,b)) -> (b,b)
      pfix2 pf f = (pf (\a -> fst (f (a, pf (\b -> snd (f (a, b)))))),
                    pf (\b -> snd (f (pf (\a -> fst (f (a, b))), b))))

      pfix4 = pfix2 (pfix2 pfix)

instance Grammar m p => Grammar m (NormSP p) where
  prule (NormSP ss sn ns nn) = NormSP <$> (prule ss) <*> (prule sn) <*> (prule ns) <*> (prule nn)

-- to optimize empty <|> a and (pure f <*> m) 
data OptEP p a = OptEmpty (Maybe String) 
               | OptPure  a 
               | OptOther (p a)

instance Functor p => Functor (OptEP p) where
  fmap f (OptEmpty s)     = OptEmpty s 
  fmap f (OptPure a)      = OptPure (f a)
  fmap f (OptOther x)     = OptOther (fmap f x)

instance Applicative p => Applicative (OptEP p) where
  pure a = OptPure a

  OptEmpty s1 <*> OptEmpty s2 = OptEmpty (s1 `mappend` s2)
  OptEmpty s1 <*> _           = OptEmpty s1
  _           <*> OptEmpty s2 = OptEmpty s2 
  OptPure f   <*> OptPure a   = OptPure  (f a)
  OptPure f   <*> OptOther x  = OptOther (fmap f x)
  OptOther mf <*> OptPure a   = OptOther (fmap ($ a) mf)
  OptOther mf <*> OptOther ma = OptOther (mf <*> ma)

instance Alternative p => Alternative (OptEP p) where
  empty = OptEmpty Nothing

  OptEmpty _ <|> p          = p
  p          <|> OptEmpty _ = p 
  OptPure  a <|> OptPure  b = OptOther (pure a <|> pure b)
  OptPure  a <|> OptOther p = OptOther (pure a <|> p)
  OptOther p <|> OptPure  b = OptOther (p <|> pure b)
  OptOther p <|> OptOther q = OptOther (p <|> q)

instance ParserLike p => ParserLike (OptEP p) where
  psatisfy q = OptOther (psatisfy q)
  pchar c    = OptOther (pchar c)

  ptext []   = OptPure []
  ptext s    = OptOther (ptext s)

  pfail s    = OptEmpty (Just s)
  pspaces    = OptOther (pspaces)

instance ParserFix p => ParserFix (OptEP p) where
  pfix f =
    case f (OptEmpty Nothing) of
      OptEmpty Nothing  -> empty
      OptEmpty (Just s) -> pfail s
      _ -> case f (OptOther empty) of
             OptPure a -> OptPure a
             _ -> 
               OptOther $ pfix  (\x ->
                            case f (OptOther x) of
                              OptEmpty Nothing  -> empty
                              OptEmpty (Just s) -> (pfail s)
                              OptPure  a        -> (pure a)
                              OptOther y        -> y)
  

runOptEP :: ParserLike p => OptEP p a -> p a
runOptEP (OptOther p) = p
runOptEP (OptEmpty Nothing)  = empty
runOptEP (OptEmpty (Just s)) = pfail s
runOptEP (OptPure  a)        = pure a
  
instance Grammar m p => Grammar m (OptEP p) where
  prule p = OptOther <$> prule (runOptEP p)
  -- prule (OptOther p) = OptOther <$> prule p
  -- prule (OptEmpty s) = return $ OptEmpty s
  -- prule (OptPure a)  = return $ OptPure a 
                                   

normalizeSpacesParser :: ParserFix p => NormSP p a -> p a 
normalizeSpacesParser (NormSP p1 p2 p3 p4) = p3 <|> p4 

normalizeSpacesGrammar :: (ParserFix p, Grammar m p) => m (NormSP p a) -> m (p a)
normalizeSpacesGrammar m = fmap normalizeSpacesParser m 

-- normalizeGrammarSP ::
--   forall m a. 
--     (forall p. (Grammar m p, ParserFix p) => m (p a)) ->
--     (forall p. (Grammar m p, ParserFix p) => m (p a))
-- normalizeGrammarSP m = normalizeGrammar m


normalizeParser:: ParserFix p => NormSP (OptEP p) a -> p a
normalizeParser m =
  runOptEP (normalizeSpacesParser m)
    
normalizeGrammar :: (Grammar m p, ParserFix p) => m (NormSP (OptEP p) a) -> m (p a)
normalizeGrammar m = fmap normalizeParser m

{-

P0 = [ _ P0 _ ] | ""

"[" NN = "[
"[" NS = 0
"[" SN = "["
"[" SS = 0

_ NN = 0
_ NS = _
_ SN = 0
_ SS =

"[_" NN = 0
"[_" NS = "[_"
"[_" SN = 0
"[_" SS = "[_"

[_P0 NN = "[_" P0_SN
[_P0 NS = "[_" P0_SS
[_P0 SN = "[_" P0_SN
[_P0 SS = "[_" P0_SS 

[_P0_ NN = 0
[_P0_ NS = ([_ P0_SN _ | [_ P0_SS)
[_P0_ SN = 0
[_p0_ SS = ([_ P0_SN _ | [_ P0_SS)

[_P0_] NN = ([_ P0_SN _ | [_ P0_SS) ]
[_P0_] NS = 0
[_P0_] SN = ([_ P0_SN _ | [_ P0_SS) ]
[_P0_] SS = 0

"" NN = ""
"" NS = 0
"" SN = 0
"" SS = ""

P0_NN = ([_ P0_SN _ | [_ P0_SS) ] | ""
P0_NS = 0
P0_SN = ([_ P0_SN _ | [_ P0_SS) ]
P0_SS = ""


P0_NN = 
P0_SN = "[" _ P0_SN _ "]" | "[" _ "]"


-}
                                         
    


{-
 _ -spaces-> S
 _ -c-> N 
-}

  
      
  
  


  
      
  
  




  
  
  




-- {-

-- -}

-- data Norm p a = Norm    Bool Bool (p a) 
--               | NormSP  Bool (p a)      -- unit of spaces 

-- addSpacesL :: ParserLike p => p a -> p a
-- addSpacesL = (pspaces *>)

-- addSpacesR :: ParserLike p => p a -> p a
-- addSpacesR = (<* pspaces) 

-- instance Functor p => Functor (Norm p) where
--   fmap f (Norm l r x) = Norm l r (fmap f x)
--   fmap f (NormSP b x) = NormSP b (fmap f x)
  
-- instance ParserLike p => Applicative (Norm p) where
--   pure a = NormSP False (pure a)

--   NormSP b f <*> NormSP b' a  = NormSP (b || b') (f <*> a)
--   NormSP b f <*> Norm l2 r2 a
--     | l2        = Norm l2 r2 (f <*> a)
--     | otherwise = Norm (b || l2) r2 (f <*> a)

--   Norm l1 r1 f <*> NormSP b a
--     | r1        = Norm l1 r1 (f <*> a)
--     | otherwise = Norm l1 (b || r1) (f <*> a)

--   Norm l1 r1 f <*> Norm l2 r2 g = Norm l1 r2 (f <*> (if r1 || l2 then addSpacesL g else g))

-- instance ParserLike p => Alternative (Norm p) where
--   empty = Norm False False empty 

--   NormSP b1 p1 <|> NormSP b2 p2 = NormSP (b1 || b2) (p1 <|> p2)
--   NormSP b1 p1 <|> p = Norm b1 b1 p1 <|> p
--   Norm l1 r1 d1 <|> NormSP b p = Norm l1 r1 d1 <|> Norm b b p 
--   Norm l1 r1 d1 <|> Norm l2 r2 d2 
--     | l1 == l2 && r1 == r2 = Norm l1 r1 (d1 <|> d2)
--     | l1 == l2 && r1 /= r2 =
--         Norm l1 False (addSpR r1 d1 <|> addSpR r2 d2)
--     | l1 /= l2 && r1 == r2 =
--         Norm False r2 (addSpL l1 d1 <|> addSpL l2 d2)
--     | otherwise =
--         Norm False False (addSpL l1 (addSpR r1 d1) <|> addSpL l2 (addSpR r2 d2)) 
--     where
--       addSpL b = if b then addSpacesL else id
--       addSpR b = if b then addSpacesR else id 

-- instance ParserLike p => ParserLike (Norm p) where
--   psatisfy cond = Norm False False (psatisfy cond)     
--   pspaces = NormSP True (pure ())

--   pfail s = Norm False False (pfail s)
  
--   pfix f =
--     let g d = case f (Norm False False d) of
--                 NormSP b p -> if b then (p <* pspaces) else p
--                 Norm l r p -> (if l then addSpacesL else id) $ (if r then addSpacesR  else id) $ p
--     in Norm False False (pfix g)

-- instance Grammar m p => Grammar m (Norm p) where
--   prule p =
--     case p of
--       NormSP b p -> NormSP b <$> (prule p)
--       Norm l r p -> Norm l r <$> (prule p)

type NTName = Int 
-- data PDoc a = PDoc (Maybe NTName) ([NTName] -> Int -> Precedence -> Doc) 

-- runPDoc (PDoc (Just nt) f) visited n k =
--   if nt `elem` visited then
--     text ("Q" ++ show nt)
--   else
--     parensIf (k > 1) $ 
--       text "μ" <> text ("Q" ++ show nt) <> text "."
--       <> nest 2 (group (linebreak <> (f (nt:visited) n 1)))
-- runPDoc (PDoc _         f) visited n k = f visited n k  

-- instance Functor PDoc where
--   fmap f (PDoc nt p) = PDoc nt p

-- instance Applicative PDoc where
--   pure a  = PDoc Nothing $ \_ _ _ -> D.text (show "")
--   p <*> q = PDoc Nothing $ \vs n k -> parensIf (k > 2) $ runPDoc p vs n 2 <+> runPDoc q vs n 2

-- instance Alternative PDoc where
--   empty = PDoc Nothing $ \_ _ _ -> text (show 0)

--   p <|> q =
--     PDoc Nothing $ \vs n k -> parensIf (k > 1) $ (runPDoc p vs n 1 </> text "|" <+> runPDoc q vs n 1)

-- instance ParserLike PDoc where
--   psatisfy cond = PDoc Nothing $ \_ _ _ -> text "{...}"
--   pchar c = PDoc Nothing $ \_ _ _ -> text (show c)
--   ptext s = PDoc Nothing $ \_ _ _ -> text (show s)

--   pspaces = PDoc Nothing $ \_ _ _ -> text "_"

--   pfail s = empty 

-- instance ParserFix PDoc where 
--   pfix f = PDoc Nothing $ \vs n k ->
--                     let nt = "P" ++ show n 
--                     in parensIf (k > 0) $
--                          text "μ" <> text nt <> text "." <>
--                          nest 2 (group (linebreak <> runPDoc (f (PDoc Nothing $ \_ _ _ -> text nt)) vs (n+1) 0))

data NTGen a = NTGen (Int -> (a, Int))

newName :: NTGen Int
newName = NTGen $ \i -> (i, i+1)

instance Functor NTGen where
  fmap f (NTGen k) = NTGen $ first f . k

instance Applicative NTGen where
  pure = return
  mf <*> mx = do
    f <- mf
    x <- mx
    return $ f x

instance Monad NTGen where
  return a = NTGen $ \i -> (a, i)
  NTGen k >>= f = NTGen $ \i ->
                            let (a, i') = k i
                                NTGen h = f a
                            in h i'

instance MonadFix NTGen where
  mfix f = NTGen $ \j -> let (a, i) = let NTGen h = f a in h j 
                         in (a, i)

-- instance Grammar NTGen PDoc where
--   prule (PDoc _ d) = do
--     n <- newName
--     return $ PDoc (Just n) d 
                            
-- pprParser :: PDoc a -> Doc
-- pprParser p = runPDoc p [] 0 0

-- pprGrammar :: NTGen (PDoc a) -> Doc
-- pprGrammar mp =
--   case mp of
--     NTGen k -> runPDoc (fst (k 0)) [] 0 0 

type NTNameMap a = IM.IntMap a 

memberNM :: NTName -> NTNameMap a -> Bool 
memberNM = IM.member

insertNM :: NTName -> a -> NTNameMap a -> NTNameMap a
insertNM = IM.insert 

emptyNM :: NTNameMap a
emptyNM = IM.empty 

newtype PDocD a = PDocD PDocDImpl
data PDocDImpl = PMarked NTName PDocDImpl 
               | PSem    (Int -> Precedence -> State (NTNameMap Doc) Doc)


instance Functor PDocD where
  fmap f (PDocD i)    = PDocD i


pprName :: NTName -> Doc
pprName nt = text $ "Q" ++ show nt 



runPDocD :: PDocD a -> Int -> Precedence -> State (NTNameMap Doc) Doc 
runPDocD (PDocD d) = go d
  where
    go (PSem h) n k = h n k 
    go (PMarked nt r) n k = do
      table <- get
      (if nt `memberNM` table then
          return (pprName nt)
       else do 
          put (insertNM nt D.empty table)
          d <- go r n 0
          modify (insertNM nt d)
          return (pprName nt))

  -- case d of
  --   PMarked nt r | nt `elems` vs -> return (mkName nt)
  --                | otherwise     -> do
  --                    d <- runPDocD r (nt : vs) n 0
  --                    tell [(mkName nt, d)]
  --                    return (mkName nt)
  --   PSem h -> h vs n k 
  -- where
  --   mkName nt = text $ "Q" ++ show nt

-- runPDocD :: PDocD a -> [NTName] -> Int -> Precedence -> Writer [(Doc,Doc)] Doc 
-- runPDocD ~(PDocD c h) vs n k =
--   case c of
--     Just nt | nt `elem` vs ->
--                 return (mkName nt)
--     Just nt | otherwise -> do
--                 d <- h (nt : vs) n 0
--                 tell [(mkName nt,d)]
--                 return (mkName nt)
--     _ -> 
--       h vs n k 
--   where
--     mkName nt = text $ "Q" ++ show nt
  
instance Applicative PDocD where
  pure a = 
    PDocD (PSem (\_ _ -> return $ text (show "")))
  p <*> q = 
    PDocD $ PSem $ \n k ->
    parensIf (k > 2) <$> (liftM2 (<+>) (runPDocD p n 2)
                                       (runPDocD q n 2))

instance Alternative PDocD where
  empty = PDocD $ PSem $ \_ _ ->
    return $ text "∅"

  p <|> q = PDocD $ PSem $ \n k -> do
    d1 <- runPDocD p n 1
    d2 <- runPDocD q n 1
    return $ parensIf (k > 1) $ group (d1 // text "|" <+> d2)

instance ParserLike PDocD where
  psatisfy cond = PDocD $ PSem $ \_ _ ->
    return $ text "#"

  pchar c = PDocD $ PSem $ \_ _ ->
    return $ text (show c)

  ptext s = PDocD $ PSem $ \_ _ ->
    return $ text (show s)

  pspaces = PDocD $ PSem $ \_ _ ->
    return $ text "_"

  pfail s = empty 
                            

instance ParserFix PDocD where
  pfix f = PDocD $ PSem $ \n k -> do 
    let nd = text ("P" ++ show n)
    body <- runPDocD (f (PDocD $ PSem $ \_ _ -> return nd)) (n+1) 0
    return $ parensIf (k > 0) $ text "μ" <> nd <> text "." <> group body 


instance Grammar NTGen PDocD where
  prule (PDocD d) = do
    n <- newName
    return $ PDocD (PMarked n d)

                      
pprParser ::  PDocD a -> Doc 
pprParser p = 
  let (d, ds) = second IM.toList $ runState (runPDocD p 0 0) emptyNM
  in case ds of
       [] -> d
       _  -> d <+> 
             nest 2 (linebreak <> text "where") <>
             nest 4 (line <> punctuate linebreak (map pprRule ds))
  where
    pprRule (a,b) = pprName a <+> text "-->" <+> align b 
    
pprGrammar :: NTGen (PDocD a) -> Doc
pprGrammar (NTGen k) = pprParser (fst (k 0))


testParens :: ParserFix p => p ()
testParens =
  pfix (\p -> ptext "[" *> pspaces *> p <* pspaces <* ptext "]"
             <|> pure ())

{-
P0 --> "[" _ P0 _ "]"
   -->

P0_SS -> "[" _ P0_NS 
-}


data BT = L | N BT BT 

test1 :: ParserFix p => p BT 
test1 =
  pfix (\p -> L <$ ptext "*"
              <|> N <$ ptext "(" <*> p <*> p <* ptext ")")

test2 :: Grammar m p => m (p BT)
test2 = do 
  rec p <- prule $
           L <$ ptext "*"
           <|> N <$ ptext "(" <*> p <*> p <* ptext ")"
  return p 
                      
data RT = Node String [RT]

test3 :: ParserFix p => p RT
test3 =
  let alphas = pfix $ \alphas ->
                        pure []
                        <|>
                        (:) <$> oneOf ['a'..'z'] <*> alphas
  in pfix $ \p ->
    let pp = pfix $ \pp ->
                      pure []
                      <|>
                      (:) <$> p <* pspaces <* ptext ";" <* pspaces <*> pp
    in Node <$> alphas <* ptext "[" <* pspaces <*> pp <* pspaces <* ptext "]" 
  where
    oneOf [] = empty
    oneOf (c:cs) = pchar c <|> oneOf cs 

test4 :: Grammar m p => m (p RT)
test4 = do 
  rec alphas <- prule $ pure []
                <|>
                (:) <$> oneOf ['a'..'z'] <*> alphas
      pp <- prule $ pure []
            <|>
            (:) <$> p <* pspaces <* ptext ";" <* pspaces <*> pp
      p  <- prule $ Node <$> alphas <* ptext "[" <* pspaces <*> pp <* pspaces <* ptext "]"
  return p
    where
      oneOf []     = empty
      oneOf [c]    = pchar c 
      oneOf (c:cs) = pchar c <|> oneOf cs 


