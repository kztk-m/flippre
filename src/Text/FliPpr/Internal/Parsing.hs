{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}


{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE GADTs #-}
module Text.FliPpr.Internal.Parsing where

-- import Text.FliPpr.Internal.Type
import Control.Monad.Writer hiding ((<>))
import Control.Monad.Identity 

import Data.Typeable 
import Control.Applicative
-- import Data.Char

import Data.Maybe (fromJust)
import Data.Functor.Compose

import Prelude hiding (lookup) 

-- import Control.Monad.ST
-- import Data.STRef 

-- import Data.Kind 
-- import Data.Coerce

import Text.FliPpr.Doc as D hiding (empty) 
import qualified Text.FliPpr.Doc as D
-- import Text.FliPpr.Fix as F
import Text.FliPpr.Internal.Type (Apps(..), TypeList(..))

import qualified Data.Map as M

class (Applicative p, Alternative p) => ParserLike p where
  pchar :: Char -> p Char
  pchar c = psatisfy (== c)
                       
  psatisfy :: (Char -> Bool) -> p Char 

  ptext :: String -> p String
  ptext []     = pure []
  ptext (c:cs) = (:) <$> pchar c <*> ptext cs 

  pfail :: String -> p a 

  -- for efficient manipulalation
  pspace  :: p () 
  pspaces :: p ()
  -- pspaces = pfix (\x -> void (ptext "") <|> (space *> x))
  --   where
  --     space = psatisfy (isSpace)

class (Functor q, Show (Key q)) => FinContainer q where
  data Key q :: *
  members      :: q a -> [(Key q, a)]
  lookup       :: Key q -> q a -> Maybe a
  -- singleton    :: Key q -> a -> q a
  fromFunction :: (Key q -> a) -> q a 


instance (Show (Key p), Show (Key q)) => Show (Key (Compose p q)) where
  show (KCompose k1 k2) = "C" ++ show k1 ++ "_" ++ show k2 

instance (FinContainer p, FinContainer q) => FinContainer (Compose p q) where
  data Key (Compose p q) = KCompose (Key p) (Key q)

  members (Compose t) =
    [ (KCompose k k', v) | (k,tq) <- members t, (k',v) <- members tq ]

  lookup (KCompose p q) (Compose t) = lookup p t >>= lookup q
  -- singleton (KCompose p q) v = Compose $ singleton p (singleton q v) 

  fromFunction f = Compose $ fromFunction (\k -> fromFunction (\k' -> f (KCompose k k')))


-- instance Ord k => FinContainer (M.Map k) where
--   data Key (M.Map k) = KM k

--   members t = [ (KM k, v) | (k,v) <- M.toList t ]

--   lookup (KM k) m = M.lookup k m
--   -- singleton (KM k) v = M.singleton k v 
  
-- instance FinContainer IM.IntMap where
--   data Key IM.IntMap = KI Int

--   members t = [ (KI i, v) | (i,v) <- IM.toList t ]
--   lookup (KI i) m = IM.lookup i m
--   singleton (KI i) v = IM.singleton i v 

instance FinContainer Identity where
  data Key Identity = KIdentity 

  members (Identity a) = [(KIdentity , a)]
  lookup _ (Identity a) = Just a
  -- singleton _ v = Identity v
  fromFunction f = Identity (f KIdentity)

instance (Show (Key Identity)) where
  show (KIdentity) = "0" 

class ParserLike p => ParserFix p  where
  pfix  :: (FinContainer q, TypeList ts)
           => (Apps (Compose q p) ts -> Apps (Compose q p) ts) ->
              (Apps (Compose q p) ts -> q (p r)) -> q (p r)


pfix1 :: ParserFix p => (p a -> p a) -> p a
pfix1 f = runIdentity $ pfix f' k 
  where
    -- k :: Apps (Compose Identity p) '[a] -> Identity (p a)
    k (Compose x :> End) = x 

    -- f' :: Apps (Compose Identity p) '[a] -> Apps (Compose Identity p) '[a]
    f' = to . f . from

    to :: p a -> Apps (Compose Identity p) '[a]
    to x = Compose (Identity x) :> End 

    from :: Apps (Compose Identity p) '[a] -> p a
    from (Compose (Identity x) :> End) = x 
    

-- class (ParserLike p, MonadFix m) => Grammar m p where
--   prec :: p a -> m (p a) 


-- -- an interpretation to replace pfix by prule.
-- newtype LiftRec m p a = LiftRec { unLiftRec :: m (p a) }

-- instance (Functor m, Functor p) => Functor (LiftRec m p) where
--   fmap f (LiftRec m) = LiftRec (fmap (fmap f) m)

-- instance (Applicative m, Applicative p) => Applicative (LiftRec m p) where
--   pure = LiftRec . pure . pure
--   LiftRec mf <*> LiftRec ma =
--     LiftRec $ liftA2 (<*>) mf ma  

-- instance (Applicative m, Alternative p) => Alternative (LiftRec m p) where
--   empty = LiftRec (pure empty)
--   LiftRec ma <|> LiftRec mb =
--     LiftRec $ liftA2 (<|>) ma mb

-- instance (Applicative m, ParserLike p) => ParserLike (LiftRec m p) where
--   pchar c    = LiftRec (pure (pchar c))
--   psatisfy q = LiftRec (pure (psatisfy q))
--   pfail s    = LiftRec (pure (pfail s))

--   ptext s    = LiftRec (pure (ptext s))
  
--   pspaces    = LiftRec (pure pspaces)


-- instance Grammar m p => ParserFix (LiftRec m p) where
--   pfix f = LiftRec $ do
--     let k a = let LiftRec m = f (LiftRec (return a))
--               in m >>= prule
--     mfix k

-- instance Grammar m p => Grammar m (LiftRec m p) where
--   prule (LiftRec m) = fmap (LiftRec . prule) m


-- liftFix :: (forall p. (ParserFix p, Grammar m p) => p a) ->
--            (forall p. (ParserLike p, Grammar m p) => m (p a))
-- liftFix m =
--   case m of
--     LiftRec x -> x 


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


{-
Consider the transducer:

  qN pspace  -> qS
  qN pspaces -> qSS
  qN a       -> a qN 

  qS pspace  -> pspace qS
  qS pspaces -> pspace qSS
  qS a       -> pspace qN

  qSS pspace  -> pspace  qSS 
  qSS pspaces -> qSS
  qSS a       -> pspaces qN

-}

data SpMode = SpN  -- corresponding to qN above
            | SpS  -- corresponding to qS above 
            | SpSS -- corresponding to qSS above
            deriving (Eq, Show, Ord, Enum, Bounded)

newtype NormSP p a = NormSP { unNormSP :: M.Map (SpMode, SpMode) (p a) }

instance Functor p => Functor (NormSP p) where
  fmap f (NormSP x) = NormSP (fmap (fmap f) x)

lookupTrans :: Alternative p => SpMode -> SpMode -> (NormSP p a) -> p a
lookupTrans p q (NormSP x) =
  case M.lookup (p,q) x of
    Just v  -> v
    Nothing -> empty 

instance Alternative p => Applicative (NormSP p) where
  pure a = NormSP $ M.fromList [ ((p,p), pure a) | p <- [SpN, SpS, SpSS ] ]

  NormSP x <*> NormSP y = NormSP $
    M.fromListWith (<|>) [ ((p,q), f <*> a) | ((p,r),f) <- M.toList x, ((r',q),a) <- M.toList y, r == r' ]

instance Alternative p => Alternative (NormSP p) where
  empty = NormSP $ M.empty
  NormSP x <|> NormSP y = NormSP $ M.unionWith (<|>) x y 

transitN :: ParserLike p => p a -> NormSP p a
transitN p = NormSP $ 
  M.fromList [ ((SpN,  SpN), p),
               ((SpS,  SpN), pspace *> p),
               ((SpSS, SpN), pspaces *> p) ]


instance ParserLike p => ParserLike (NormSP p) where
  psatisfy cond = transitN (psatisfy cond)

  pchar c = transitN (pchar c) 

  ptext "" = pure ""
  ptext s  = transitN (ptext s)


  pfail s = NormSP $
    M.fromList [ ((p,q), pfail s) |
                 p <- [SpN, SpS, SpSS],
                 q <- [SpN, SpS, SpSS] ]

  pspace = NormSP $
    M.fromList [ ((SpN,  SpS),  pure ()),
                 ((SpS,  SpS),  pspace ),
                 ((SpSS, SpSS), pspace ) ]

  pspaces = NormSP $
    M.fromList [ ((SpN,  SpSS), pure ()),
                 ((SpS,  SpSS), pspace ),
                 ((SpSS, SpSS), pure ()) ]


newtype NM a = NM { unNM :: M.Map (SpMode, SpMode) a }
  deriving (Functor)

instance FinContainer NM where
  data Key NM = KNM (SpMode, SpMode)

  members (NM x) = [ (KNM k, v) | (k,v) <- M.toList x ]
  lookup (KNM k) (NM x) = M.lookup k x 
  fromFunction f = NM $ M.fromList [ ((k1,k2),f (KNM (k1,k2))) |
                                     k1 <- [ SpN, SpS, SpSS ],
                                     k2 <- [ SpN, SpS, SpSS ] ] 
  
instance Show (Key NM) where
  show (KNM (k1,k2)) = "P" ++ show k1 ++ "_" ++ show k2

  
instance ParserFix p => ParserFix (NormSP p) where
  pfix :: forall (q :: * -> *) ts r.
                  (FinContainer q, TypeList ts) =>
                  (Apps (Compose q (NormSP p)) ts -> Apps (Compose q (NormSP p)) ts)
                  -> (Apps (Compose q (NormSP p)) ts -> q (NormSP p r))
                  -> q (NormSP p r)
  pfix f k = NormSP . unNM <$> (getCompose $ pfix f' k')
    where
      f' :: Apps (Compose (Compose q NM) p) ts -> Apps (Compose (Compose q NM) p) ts
      f' = mapApps from . f . mapApps to

      k' :: Apps (Compose (Compose q NM) p) ts -> Compose q NM (p r)
      k' = Compose . fmap (NM . unNormSP) . k . mapApps to
      from :: Functor q => Compose q (NormSP p) a -> Compose (Compose q NM) p a
      from (Compose t) =
        Compose $ Compose $ fmap (NM . unNormSP) t 

      to :: Functor q => Compose (Compose q NM) p a -> Compose q (NormSP p) a
      to (Compose (Compose t)) = Compose $ fmap (NormSP . unNM) t 
      

  
  -- pfix f = toMap $ F.fix (fromMap . f . toMap)
  --   where
  --     dom  = [SpN, SpS, SpSS]
  --     keys = [(p,q) | p <- dom, q <- dom ]
  --     toMap f   = NormSP $ M.fromAscList [ (k, unPFix (f k)) | k <- keys ]
  --     fromMap (NormSP m) = \k -> PFix $ fromJust (M.lookup k m)

normalizeSpacesParser :: ParserFix p => NormSP p a -> p a
normalizeSpacesParser m = 
  lookupTrans SpN SpN m
  <|> lookupTrans SpN SpS m <* pspace
  <|> lookupTrans SpS SpSS m <* pspaces 
  

newtype NormSPC p a = NormSPC { unNormSPC :: forall r. SpMode -> p (a -> r) -> p (a -> r) -> p (a -> r) -> p r }

instance Functor p => Functor (NormSPC p) where
  fmap f (NormSPC h) = NormSPC $ \m kn ks kss -> h m (fmap (.f) kn) (fmap (.f) ks) (fmap (.f) kss)

instance Alternative p => Applicative (NormSPC p) where
  pure a = NormSPC $ \m kn ks kss ->
    case m of
      SpN  -> kn  <*> pure a
      SpS  -> ks  <*> pure a
      SpSS -> kss <*> pure a


  x <*> y = NormSPC $ \m kn ks kss ->
    let kn'  = fmap (\b2r a a2b -> b2r (a2b a)) kn
        ks'  = fmap (\b2r a a2b -> b2r (a2b a)) ks
        kss' = fmap (\b2r a a2b -> b2r (a2b a)) kss
    in
    unNormSPC x m
      (unNormSPC y SpN  kn' ks' kss')
      (unNormSPC y SpS  kn' ks' kss')
      (unNormSPC y SpSS kn' ks' kss')

instance Alternative p => Alternative (NormSPC p) where
  empty = NormSPC $ \_ _ _ _ -> empty

  x <|> y = NormSPC $ \m kn ks kss -> 
    unNormSPC x m kn ks kss <|> unNormSPC y m kn ks kss


transitNC d SpN  kn ks kss = kn <*> d
transitNC d SpS  kn ks kss = ks <*> (pspace *> d)
transitNC d SpSS kn ks kss = kss <*> (pspaces *> d)

instance ParserLike p => ParserLike (NormSPC p) where
  psatisfy cond = NormSPC $ transitNC (psatisfy cond)
  pchar c = NormSPC $ transitNC (pchar c)
  ptext "" = pure ""
  ptext s = NormSPC $ transitNC (ptext s)
  pfail s = NormSPC $ \_ _ _ _ -> pfail s

  pspace = NormSPC $ \m kn ks kss ->
    case m of
      SpN  -> ks <*> pure () 
      SpS  -> ks <*> pspace
      SpSS -> kss <*> pspace

  pspaces = NormSPC $ \m kn ks kss ->
    case m of
      SpN  -> kss <*> pure ()
      SpS  -> kss <*> pspace
      SpSS -> kss <*> pure () 
    
-- memoizeNormSP :: NormSP p a -> NormSP p a
-- memoizeNormSP (NormSP h) = NormSP h'
--   where
--     i SpN  = 0
--     i SpS  = 1
--     i SpSS = 2 
--     h' p q = hs !! (i p * 3 + i q)

--     hs = [ h p q | p <- [SpN, SpS, SpSS], q <- [SpN, SpS, SpSS] ]
    

-- instance Functor p => Functor (NormSP p) where
--   fmap f (NormSP h) = NormSP (\s e -> fmap f (h s e))

-- instance Alternative p => Applicative (NormSP p) where
--   -- the empty string does not change the state 
--   pure a = NormSP (\q q' -> if q == q' then pure a else empty) 

--   -- computes the transition
--   NormSP x <*> NormSP y = memoizeNormSP $ 
--     NormSP $ \p q -> foldr1 (<|>) [ x p r <*> y r q | r <- [SpN, SpS, SpSS] ]

-- instance Alternative p => Alternative (NormSP p) where
--   -- empty is empty 
--   empty = NormSP (\_ _ -> empty) 

--   NormSP x <|> NormSP y = memoizeNormSP $ 
--     NormSP $ \p q -> x p q <|> y p q 

-- transitN x p q =
--   case q of
--     SpN ->
--       case p of
--         SpN  -> x
--         SpS  -> pspace  *> x
--         SpSS -> pspaces *> x
--     _ -> empty 
    
-- instance ParserLike p => ParserLike (NormSP p) where
--   psatisfy cond = NormSP $ transitN (psatisfy cond)

--   pchar c = NormSP $ transitN (pchar c) 

--   ptext "" = pure ""
--   ptext s  = NormSP $ transitN (ptext s)

--   pfail s = NormSP $ \_ _ -> pfail s

--   pspace = NormSP f
--     where
--       f SpN SpS   = pure ()
--       f SpN _     = empty
--       f SpS SpS   = pspace
--       f SpS _     = empty
--       f SpSS SpSS = pspace
--       f SpSS _    = empty

--   pspaces = NormSP f
--     where
--       f SpN SpSS  = pure ()
--       f SpN _     = empty

--       f SpS SpSS  = pspace
--       f SpS _     = empty

--       f SpSS SpSS = pure ()
--       f SpSS _    = empty  
  

-- -- \p q -> f (g p q)
-- -- = \p q -> (f . (g p)) q
-- -- = \p -> (f . (g p))
-- -- = \p -> ((f.) (g p))
-- -- = \p -> (((f.).g)) p
-- -- = (f.) . g 
        

-- instance ParserFix p => ParserFix (NormSP p) where
--   pfix f = memoizeNormSP $ NormSP $ (unPFix .) . 
--                                      (F.fix $ \x a b -> trace (show (a,b)) $ 
--                                                 let NormSP k = f (NormSP $ (unPFix .) . x)
--                                                 in PFix (k a b))




-- data NormSP p a = NormSP { normSPss :: (p a) -- parser that occurs after spaces, ends with spaces
--                          , normSPsn :: (p a) -- parser that occurs after spaces, ends without spaces
--                          , normSPns :: (p a) -- parser that does not occur after spaces, ends with spaces
--                          , normSPnn :: (p a) } -- parser that does not occur after spaces, ends without spaces
                  
-- instance Functor p => Functor (NormSP p) where
--   fmap f (NormSP p1 p2 p3 p4) = NormSP (fmap f p1) (fmap f p2) (fmap f p3) (fmap f p4)

-- instance Alternative p => Applicative (NormSP p) where
--   pure a = NormSP (pure a) empty empty (pure a)
--   p1 <*> p2 =
--     NormSP { normSPss = normSPss p1 <*> normSPss p2 
--                         <|> normSPsn p1 <*> normSPns p2
--            , normSPsn = normSPss p1 <*> normSPsn p2
--                         <|> normSPsn p1 <*> normSPnn p2
--            , normSPns = normSPns p1 <*> normSPss p2
--                         <|> normSPnn p1 <*> normSPns p2
--            , normSPnn = normSPns p1 <*> normSPsn p2
--                         <|> normSPnn p1 <*> normSPnn p2 }

-- instance Alternative p => Alternative (NormSP p) where
--   empty = NormSP empty empty empty empty
--   p1 <|> p2 =
--     NormSP { normSPss = normSPss p1 <|> normSPss p2
--            , normSPsn = normSPsn p1 <|> normSPsn p2
--            , normSPns = normSPns p1 <|> normSPns p2
--            , normSPnn = normSPnn p1 <|> normSPnn p2 } 

-- instance ParserLike p => ParserLike (NormSP p) where
--   psatisfy q =
--     NormSP { normSPss = empty
--            , normSPsn = psatisfy q
--            , normSPns = empty
--            , normSPnn = psatisfy q }
--   pchar c    =
--     NormSP { normSPss = empty
--            , normSPsn = pchar c
--            , normSPns = empty
--            , normSPnn = pchar c }

--   ptext []   = pure [] 
--   ptext s    =
--     NormSP { normSPss = empty
--            , normSPsn = ptext s
--            , normSPns = empty
--            , normSPnn = ptext s }

--   pfail s    = NormSP (pfail s) (pfail s) (pfail s) (pfail s)


--   pspace     =
--     NormSP { normSPss = pspace -- since  (pspaces pspace pspaces) = pspaces pspace 
--            , normSPsn = pure ()
--            , normSPns = empty
--            , normSPnn = pspace } 
             
--   pspaces    =
--     NormSP { normSPss = pure ()
--            , normSPsn = empty
--            , normSPns = pspaces 
--            , normSPnn = empty } 

-- -- pfix2 :: ParserFix p => ((p a, p b) -> (p a, p b)) -> (p a, p b)
-- -- pfix2 f = (pfix (\a -> fst (f (a, pfix (\b -> snd (f (a, b)))))),
-- --            pfix (\b -> snd (f (pfix (\a -> fst (f (a, b))), b))))
          

-- instance ParserFix p => ParserFix (NormSP p) where
--   pfix f = let ((s,t),(v,w)) =
--                  pfix4 (\((a,b),(c,d)) -> let NormSP a' b' c' d' = f (NormSP a b c d)
--                                           in ((a',b'),(c',d')))
--            in NormSP s t v w 
--     where
--       pfix2 :: ((b -> b) -> b) -> ((b,b) -> (b,b)) -> (b,b)
--       pfix2 pf f = (pf (\a -> fst (f (a, pf (\b -> snd (f (a, b)))))),
--                     pf (\b -> snd (f (pf (\a -> fst (f (a, b))), b))))

--       pfix4 = pfix2 (pfix2 pfix)

-- -- instance Grammar m p => Grammar m (NormSP p) where
-- --   prule (NormSP ss sn ns nn) = NormSP <$> (prule ss) <*> (prule sn) <*> (prule ns) <*> (prule nn)

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
  pspace     = OptOther pspace 
  pspaces    = OptOther (pspaces)


data MOptEP a = MOptEmpty (Maybe String)
              | MOptOther a

instance Functor MOptEP where
  fmap f (MOptOther a) = MOptOther (f a)
  fmap f (MOptEmpty s) = MOptEmpty s 

instance Show (Key MOptEP) where
  show _ = "K"

instance FinContainer MOptEP where
  data Key MOptEP = K

  members (MOptOther a) = [(K,a)]
  members _             = []

  lookup _ (MOptOther a) = Just a
  lookup _ _             = Nothing

  fromFunction f = MOptOther (f K) 
              
instance ParserFix p => ParserFix (OptEP p) where
  pfix :: forall (q :: * -> *) ts r.
                  (FinContainer q, TypeList ts) =>
                  (Apps (Compose q (OptEP p)) ts -> Apps (Compose q (OptEP p)) ts)
                  -> (Apps (Compose q (OptEP p)) ts -> q (OptEP p r))
                  -> q (OptEP p r)
  pfix f h = fmap mo $ getCompose $ pfix f' h'
    where
      f' :: Apps (Compose (Compose q MOptEP) p) ts -> Apps (Compose (Compose q MOptEP) p) ts 
      f' = mapApps from . f . mapApps to

      h' :: Apps (Compose (Compose q MOptEP) p) ts -> Compose q MOptEP (p r)
      h' = Compose . fmap om . h . mapApps to

      om :: OptEP p a -> MOptEP (p a)
      om (OptOther p) = MOptOther p
      om (OptEmpty s) = MOptEmpty s
      om (OptPure  a) = MOptOther (pure a)

      mo (MOptOther p) = OptOther p
      mo (MOptEmpty s) = OptEmpty s 
      
      to :: Compose (Compose q MOptEP) p a -> Compose q (OptEP p) a 
      to (Compose (Compose p)) = Compose (mo <$> p)

      from :: Compose q (OptEP p) a -> Compose (Compose q MOptEP) p a 
      from (Compose p) = Compose $ Compose (om <$> p)

      unOpt (OptEmpty Nothing)  = empty
      unOpt (OptEmpty (Just s)) = pfail s
      unOpt (OptPure a)         = pure a
      unOpt (OptOther p)        = p 
        
      
    -- case f (OptEmpty Nothing) of
    --   OptEmpty Nothing  -> empty
    --   OptEmpty (Just s) -> pfail s
    --   _ -> case f (OptOther empty) of
    --          OptPure a -> OptPure a
    --          _ -> 
    --            OptOther $ pfix  (\x ->
    --                         case f (OptOther x) of
    --                           OptEmpty Nothing  -> empty
    --                           OptEmpty (Just s) -> (pfail s)
    --                           OptPure  a        -> (pure a)
    --                           OptOther y        -> y)
  

runOptEP :: ParserLike p => OptEP p a -> p a
runOptEP (OptOther p) = p
runOptEP (OptEmpty Nothing)  = empty
runOptEP (OptEmpty (Just s)) = pfail s
runOptEP (OptPure  a)        = pure a
  
-- instance Grammar m p => Grammar m (OptEP p) where
--   prule p = OptOther <$> prule (runOptEP p)
  -- prule (OptOther p) = OptOther <$> prule p
  -- prule (OptEmpty s) = return $ OptEmpty s
  -- prule (OptPure a)  = return $ OptPure a 
                                   

  
-- normalizeSpacesParser (NormSP p1 p2 p3 p4) = p3 <|> p4 

-- normalizeSpacesGrammar :: (ParserFix p, Grammar m p) => m (NormSP p a) -> m (p a)
-- normalizeSpacesGrammar m = fmap normalizeSpacesParser m 

-- normalizeGrammarSP ::
--   forall m a. 
--     (forall p. (Grammar m p, ParserFix p) => m (p a)) ->
--     (forall p. (Grammar m p, ParserFix p) => m (p a))
-- normalizeGrammarSP m = normalizeGrammar m


normalizeParser:: ParserFix p => NormSP (OptEP p) a -> p a
normalizeParser m =
  runOptEP (normalizeSpacesParser m)
    
-- normalizeGrammar :: (Grammar m p, ParserFix p) => m (NormSP (OptEP p) a) -> m (p a)
-- normalizeGrammar m = fmap normalizeParser m



newtype PDoc a = PDoc { runPDoc :: Int -> Precedence -> Doc } 

-- runPDoc (PDoc (Just nt) f) visited n k =
--   if nt `elem` visited then
--     text ("Q" ++ show nt)
--   else
--     parensIf (k > 1) $ 
--       text "μ" <> text ("Q" ++ show nt) <> text "."
--       <> nest 2 (group (linebreak <> (f (nt:visited) n 1)))
-- runPDoc (PDoc _         f) visited n k = f visited n k  

instance Functor PDoc where
  fmap f (PDoc ff) = PDoc ff

instance Applicative PDoc where
  pure a  = PDoc $ \_ _ -> D.text (show "")
  p <*> q = PDoc $ \n k -> parensIf (k > 2) $ runPDoc p n 2 <+> runPDoc q n 2
  
instance Alternative PDoc where
  empty = PDoc $ \_ _ -> text (show 0)

  p <|> q =
    PDoc $ \n k -> parensIf (k > 1) $ (runPDoc p n 1 </> text "|" <+> runPDoc q n 1)

instance ParserLike PDoc where
  psatisfy cond = PDoc $ \_ _ -> text "{...}"
  pchar c = PDoc $ \_ _ -> text (show c)
  ptext s = PDoc $ \_ _ -> text (show s)

  pspace  = PDoc $ \_ _ -> text "_"
  pspaces = PDoc $ \_ _ -> text "<SP>"

  pfail s = PDoc $ \_ _ -> text "<FAIL>" 

instance ParserFix PDoc where
  pfix :: forall (q :: * -> *) ts r.
                  (FinContainer q, TypeList ts) =>
                  (Apps (Compose q PDoc) ts -> Apps (Compose q PDoc) ts)
                  -> (Apps (Compose q PDoc) ts -> q (PDoc r))
                  -> q (PDoc r)
  pfix f cont = fromFunction $ \key -> PDoc $ \n k ->
    let pr   = Proxy :: Proxy ts 
        vars = appsInit pr (n+1) (\n' ->
                                    (Compose $ fromFunction $ \key' ->
                                        PDoc $ \_ _ -> text ("P" ++ show  n' ++ "_" ++ show key'),
                                     n'+1))
        r    = f vars
        n'   = n + appsLength pr
        rest = cont vars
        body = concatMapApps (\x -> (\y -> runPDoc  y n' 0) <$> (getCompose x))
                        (fromFunction $ \k -> text "")
                        (\x y -> fromFunction $ \k -> maybe (text "") id $ do 
                            d1 <- lookup k x
                            d2 <- lookup k y
                            return (d1 </> d2))
               $ zipWithApps (\(Compose v) (Compose r) -> Compose $ fromFunction $ \k -> PDoc $ \n pk -> 
                                 let ff v k = case lookup k v of
                                                Just res -> runPDoc res n pk 
                                                Nothing  -> text "__"
                                 in group (ff v k <+> text "=" </> align (ff r k)))
                 vars r 
    in case lookup key rest of
         Nothing -> text "" 
         Just restP -> do
           parensIf (k > 0) $ align $ 
             text "let" <+>
             align (vsep (map snd (members body))) </>
             text "in" <+> runPDoc restP n' 0 

pprParser :: PDoc a -> Doc
pprParser e = runPDoc e 0 0 

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

-- data NTGen a = NTGen (Int -> (a, Int))

-- newName :: NTGen Int
-- newName = NTGen $ \i -> (i, i+1)

-- instance Functor NTGen where
--   fmap f (NTGen k) = NTGen $ first f . k

-- instance Applicative NTGen where
--   pure = return
--   mf <*> mx = do
--     f <- mf
--     x <- mx
--     return $ f x

-- instance Monad NTGen where
--   return a = NTGen $ \i -> (a, i)
--   NTGen k >>= f = NTGen $ \i ->
--                             let (a, i') = k i
--                                 NTGen h = f a
--                             in h i'

-- instance MonadFix NTGen where
--   mfix f = NTGen $ \j -> let (a, i) = let NTGen h = f a in h j 
--                          in (a, i)

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

-- type NTNameMap a = IM.IntMap a 

-- memberNM :: NTName -> NTNameMap a -> Bool 
-- memberNM = IM.member

-- insertNM :: NTName -> a -> NTNameMap a -> NTNameMap a
-- insertNM = IM.insert 

-- emptyNM :: NTNameMap a
-- emptyNM = IM.empty 

-- newtype PDocD a = PDocD PDocDImpl
-- data PDocDImpl = PMarked NTName PDocDImpl 
--                | PSem    (Int -> Precedence -> State (NTNameMap Doc) Doc)


-- instance Functor PDocD where
--   fmap f (PDocD i)    = PDocD i


-- pprName :: NTName -> Doc
-- pprName nt = text $ "Q" ++ show nt 



-- runPDocD :: PDocD a -> Int -> Precedence -> State (NTNameMap Doc) Doc 
-- runPDocD (PDocD d) = go d
--   where
--     go (PSem h) n k = h n k 
--     go (PMarked nt r) n k = do
--       table <- get
--       (if nt `memberNM` table then
--           return (pprName nt)
--        else do 
--           put (insertNM nt D.empty table)
--           d <- go r n 0
--           modify (insertNM nt d)
--           return (pprName nt))

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
  
-- instance Applicative PDocD where
--   pure a = 
--     PDocD (PSem (\_ _ -> return $ text (show "")))
--   p <*> q = 
--     PDocD $ PSem $ \n k ->
--     parensIf (k > 2) <$> (liftM2 (<+>) (runPDocD p n 2)
--                                        (runPDocD q n 2))

-- instance Alternative PDocD where
--   empty = PDocD $ PSem $ \_ _ ->
--     return $ text "∅"

--   p <|> q = PDocD $ PSem $ \n k -> do
--     d1 <- runPDocD p n 1
--     d2 <- runPDocD q n 1
--     return $ parensIf (k > 1) $ group (d1 // text "|" <+> d2)

-- instance ParserLike PDocD where
--   psatisfy cond = PDocD $ PSem $ \_ _ ->
--     return $ text "#"

--   pchar c = PDocD $ PSem $ \_ _ ->
--     return $ text (show c)

--   ptext s = PDocD $ PSem $ \_ _ ->
--     return $ text (show s)

--   pspace  = PDocD $ PSem $ \_ _ ->
--     return $ text "_"                             

--   pspaces = PDocD $ PSem $ \_ _ ->
--     return $ text "SP"

--   pfail s = empty 
                            

-- instance ParserFix PDocD where
--   pfix f cont = fromFunction $ \key -> PDocD $ PSem $ \n k ->
--     let pr   = undefined 
--         vars = appsInit pr (n+1) (\n' ->
--                                     (Compose $ fromFunction $ \key' ->
--                                         PDocD $ PSem $ \_ _ -> text ("P" ++ show  n' ++ "_" ++ show key'),
--                                      n'+1))
--         r    = f vars
--         n'   = n + appsLength pr
--         rest = cont vars
--     in case lookup key rest of
--          Nothing -> return $ text "" 
--          Just restP -> do
--            d <- runPDocD restP n' 0 
--            return $ parensIf (k > 9) $ text "let " <+>
--              nest 2 (concatMapApps (members . getCompose) (text "") (</>)
--                       (zipWithApps (\(Compose v) (Compose r) ->
--                                       fromFunction $ \k ->
--                                        let ff v k = case lookup k v of
--                                                       Nothing -> text "__"
--                                                       Just s  -> runPDocD 
--                                        v <+> text "=" <+> align r) vars r)) <+>
--              text "in " <+> d
    
    
    
    -- PDocD $ PSem $ \n k -> do 
    -- let nd = text ("P" ++ show n)
    -- body <- runPDocD (f (PDocD $ PSem $ \_ _ -> return nd)) (n+1) 0
    -- return $ parensIf (k > 0) $ text "μ" <> nd <> text "." <> group body 


-- instance Grammar NTGen PDocD where
--   prec (PDocD d) = do
--     n <- newName
--     return $ PDocD (PMarked n d)

                      
-- pprParser ::  PDocD a -> Doc 
-- pprParser p = 
--   let (d, ds) = second IM.toList $ runState (runPDocD p 0 0) emptyNM
--   in case ds of
--        [] -> d
--        _  -> d <+> 
--              nest 2 (linebreak <> text "where") <>
--              nest 4 (line <> punctuate linebreak (map pprRule ds))
--   where
--     pprRule (a,b) = pprName a <+> text "-->" <+> align b 
    
-- pprGrammar :: NTGen (PDocD a) -> Doc
-- pprGrammar (NTGen k) = pprParser (fst (k 0))


testParens :: ParserFix p => p ()
testParens =
  pfix1 (\p -> ptext "[" *> pspaces *> p <* pspaces <* ptext "]"
              <|> pure ())

{-
P0 --> "[" _ P0 _ "]"
   -->

P0_SS -> "[" _ P0_NS 
-}


data BT = L | N BT BT 

test1 :: ParserFix p => p BT 
test1 =
  pfix1 (\p -> L <$ ptext "*"
               <|> N <$ ptext "(" <*> p <*> p <* ptext ")")

-- test2 :: Grammar m p => m (p BT)
-- test2 = do 
--   rec p <- prule $
--            L <$ ptext "*"
--            <|> N <$ ptext "(" <*> p <*> p <* ptext ")"
--   return p 
                      
data RT = Node String [RT]

test3 :: ParserFix p => p RT
test3 =
  let alphas = pfix1 $ \alphas ->
                        pure []
                        <|>
                        (:) <$> oneOf ['a'..'z'] <*> alphas
  in pfix1 $ \p ->
    let pp = pfix1 $ \pp ->
                      pure []
                      <|>
                      (:) <$> p <* pspaces <* ptext ";" <* pspaces <*> pp
    in Node <$> alphas <* ptext "[" <* pspaces <*> pp <* pspaces <* ptext "]" 
  where
    oneOf [] = empty
    oneOf (c:cs) = pchar c <|> oneOf cs 

-- test4 :: Grammar m p => m (p RT)
-- test4 = do 
--   rec alphas <- prule $ pure []
--                 <|>
--                 (:) <$> oneOf ['a'..'z'] <*> alphas
--       pp <- prule $ pure []
--             <|>
--             (:) <$> p <* pspaces <* ptext ";" <* pspaces <*> pp
--       p  <- prule $ Node <$> alphas <* ptext "[" <* pspaces <*> pp <* pspaces <* ptext "]"
--   return p
--     where
--       oneOf []     = empty
--       oneOf [c]    = pchar c 
--       oneOf (c:cs) = pchar c <|> oneOf cs 


