{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE RecursiveDo #-}

{-# OPTIONS_GHC -fwarn-unused-imports -fwarn-incomplete-patterns #-}

{-# LANGUAGE NoMonomorphismRestriction #-}

module Text.FliPpr.Internal.Type where

import Data.Kind 
import Control.Monad.State

import Data.Typeable
import Data.Coerce
import Data.Monoid    (Monoid(..))
import Data.Semigroup (Semigroup(..))

import Data.Container2 

import qualified Data.Map as M

import Control.Monad.Reader hiding (local) 
import qualified Control.Monad.Reader as RM 

import Text.FliPpr.Doc as D

import Text.FliPpr.Internal.Ref

data FType = D | Type :~> FType 


type In a = (Typeable a, Eq a)

data a <-> b = PInv String (a -> Maybe b) (b -> Maybe a) 

data Branch arg exp a (t :: FType) =
  forall b. In b => Branch (a <-> b) (arg b -> exp t)


class FliPprE (arg :: * -> *) (exp :: FType -> *) | exp -> arg where
  fapp   :: In a => exp (a :~> t) -> arg a -> exp t
  farg   :: In a => (arg a -> exp t) -> exp (a :~> t)


  fcase   :: In a => arg a -> [Branch arg exp a t] -> exp t 
  funpair :: (In a, In b) => arg (a,b) -> (arg a -> arg b -> exp t) -> exp t

  fbchoice :: exp D -> exp D -> exp D

  ftext  :: String -> exp D
  fempty :: exp D
  fcat   :: exp D -> exp D -> exp D

  -- For optimization purpose.
  fspace     :: exp D 
  fspaces    :: exp D

  
  fline      :: exp D -- translated to @text " " <> spaces@ in parsing 
  flinebreak :: exp D -- translated to @spaces@ in parsing

  falign :: exp D -> exp D
  fgroup :: exp D -> exp D
  fnest  :: Int -> exp D -> exp D

newtype Rec t e a = Rec { runRec :: t e -> e a }

adjustRec2 :: Container2 t =>
              (forall a. e a -> e' a) -> 
              (forall a. e' a -> e a) ->
              Rec t e a -> Rec t e' a
adjustRec2 f fi (Rec r) = Rec $ \x -> f (r (fmap2 fi x))

class (FliPprE arg exp, MonadFix m) => FliPprD m arg exp | exp -> arg, exp -> m where
  -- Using ffix to define a recursion would not be a good idea.
  -- The information is used to define a grammar generation that is
  -- to be used in "parsing" evaluation.
  --
  -- To use Earley or Frost's parser combinators it suffices to mark
  -- body of recursive functions. This is much more convient as
  -- we can use grammars via recursive do notations.
  --
  -- If such a "marking" approach would suffice for some other grammar manipulations such 
  -- as left recursion elimination or injectivity analysis, first character extraction and so on.
  -- Then, we will use "marking" approach instead of "ffix".
  --
  -- By 2017-11-18 kztk: 
  -- It turns out that "marking" approach is not useful to define local definitions.
  -- The local defintions are specially important for FliPpr, as we can
  -- define ``inlinable'' functions. A typical example is @manyParens@, a
  -- function to annotate a position to which arbitrary number of parens can be
  -- placed around. By @ffix@, such a function is easy to define. 
  --
  -- @
  -- manyParens :: FliPpr arg exp => exp D -> exp D
  -- manyParens d = ffix (\x -> d <|> parens x)
  -- @
  --
  -- However, this is hard to achieve by using the "marking" approach, as
  -- it can only define global definitions.
  --
  -- Thus, we many need both or use "marking" as a compromised alternative syntax.
  -- It seems to me that we cannot directly converted it to @ffix@ with using
  -- some compromising (Data.Dynamic, for example).
  --
  -- Anyway, @ffix@ is more general, and due to free variables, we cannot convert
  -- it to "marking" in general. Let's have both at this level.
  --
  -- By kztk @ 2017-11-25
  -- 
  -- It seems to me that it is not that straightforward to define the semantics of
  -- marking. Making a definition complex would be a not a good idea, and
  -- mutual recursions that are hard to define by 'ffix' would not appear so oftenly.
  --
  -- Tentatively, we removed the marking function. 
  --
  -- By kztk @ 2017-11-26
  -- Having single recursion unbearablely slow and not useful at all.
  -- The above description was wrong, and the following definition would suffice. 
  -- 
  -- @
  -- manyParens d = local $ do rec r <- rule $ d <? parens r
  --                           return r
  -- @
  -- 
  --
  -- By kztk @ 2017-11-26
  -- I find that using @rule@ has a problem on pretty-printing interpretation.
  -- Thus, I revisited usual ffix. We cannot avoid considering general mutual
  -- recursions as below. 
  -- 
  -- ffix  :: (exp t -> exp t) -> exp t
  --
  --
  -- By kztk @ 2017-12-22
  -- Changed its type from Oleg's comment. 
  --
  -- ffix :: Container2 f => f (Rec f exp) -> CPS exp (f exp)
  -- flet :: exp t -> CPS exp (exp t) 
  -- flet = return 
  --
  -- By kztk @ 2018-01-01
  --
  -- Changed its type to 
  fshare :: exp t -> m (exp t)
  flocal :: m (exp t) -> exp t   
  
newtype A arg a = A { unA :: arg a }
newtype E exp t = E { unE :: exp t }

newtype FliPpr t = FliPpr (forall m arg exp. FliPprD m arg exp => m (exp t))

-- flipprPure :: (forall arg exp. FliPprD arg exp => E exp t) -> FliPpr t
-- flipprPure x = FliPpr (unE x)

flippr :: (forall m arg exp. FliPprD m arg exp => m (E exp t)) -> FliPpr t
flippr x = FliPpr (unE <$> x) -- flipprPure (unC x)

spaces :: FliPprE arg exp => E exp D
spaces = E fspaces 

space :: FliPprE arg exp => E exp D
space = E fspace

arg :: (In a, FliPprE arg exp) => (A arg a -> E exp t) -> E exp (a :~> t)
arg f = E (farg (coerce f))

app :: (In a, FliPprE arg exp) => E exp (a :~> t) -> A arg a -> E exp t 
app (E f) (A a) = E (fapp f a) 

(@@) :: (In a, FliPprE arg exp) => E exp (a :~> t) -> A arg a -> E exp t 
(@@) = app

infixr 0 @@

case_ :: (In a, FliPprE arg exp) => A arg a -> [Branch (A arg) (E exp) a r] -> E exp r
case_ (A a) bs = E (fcase a (coerce bs))

unpair :: (In a, In b, FliPprE arg exp) => A arg (a,b) -> (A arg a -> A arg b -> E exp r) -> E exp r
unpair (A x) k = E $ funpair x (coerce k)

-- unpair :: (In a, In b, FliPprE arg exp) => A arg (a,b) -> C exp (A arg a, A arg b)
-- unpair (A x) = CPS $ \k -> funpair x (coerce (curry k))

-- unC :: C exp (E exp a) -> E exp a
-- unC (CPS m) = E (m unE)

(<?) :: FliPprE arg exp => E exp D -> E exp D -> E exp D
(<?) (E x) (E y) = E (fbchoice x y)

infixr 4 <?

-- share :: FliPprD arg exp => E exp t -> C exp (E exp t)
-- share e = E <$> flet (unE e)

share :: FliPprD m arg exp => E exp t -> m (E exp t)
share e = E <$> fshare (unE e) 

local :: FliPprD m arg exp => m (E exp t) -> E exp t
local m = E $ flocal (unE <$> m)
  
-- fix1 :: FliPprD arg exp => (E exp t -> E exp t) -> E exp t
-- fix1 f = E $ runCPS (ffix (Single (Rec $ \(Single f_) -> unE (f (E f_)))))
--                     (\(Single x) -> x)

-- fix2 :: FliPprD arg exp =>
--         ((E exp a, E exp b) -> (E exp a, E exp b)) -> C exp (E exp a, E exp b)
-- fix2 f = toPair <$> ffix
--          ((Rec $ \(f_ :< g_ :< End) -> unE $ fst $ f (E f_, E g_))
--           :<
--           (Rec $ \(f_ :< g_ :< End) -> unE $ snd $ f (E f_, E g_))
--           :<
--           End)
--   where
--     toPair (a :< b :< End) = (E a,E b) 

-- fixn :: (FliPprD arg exp, Container2 t) =>
--         t (Rec t (E exp)) -> C exp (t (E exp))
-- fixn defs =
--   fmap2 E <$> ffix (fmap2 (adjustRec2 unE E) defs)
                

-- fix1 :: (exp t -> E arg exp t) -> E arg exp t
-- fix1 f = runCont (mrec (\(t :> End) -> (f t :> End))) k
--   where
--     k :: Apps (E arg exp) '[a] -> E arg exp a
--     k (t :> End) = t

-- fix2 :: ( (exp a, exp b) -> (E arg exp a, E arg exp b)) -> C arg exp r (E arg exp a, E arg exp b)
-- fix2 f = fmap toPair $ mrec (fromPair . f . toPair)
--   where
--     fromPair :: forall exp a b. (exp a,exp b) -> Apps exp '[a,b]
--     fromPair ~(a,b) = a :> (b :> End)

--     toPair :: forall exp a b. Apps exp '[a,b] -> (exp a, exp b)
--     toPair ~(a :> b :> End) = (a,b)

-- fix3 :: ( (exp a, exp b, exp c) -> (E arg exp a, E arg exp b , E arg exp c) ) ->
--         C arg exp r (E arg exp a, E arg exp b , E arg exp c)
-- fix3 f = fmap toTriple $ mrec (fromTriple . f  . toTriple )

-- toTriple :: Apps exp '[a,b,c] -> (exp a, exp b, exp c) 
-- toTriple (a :> b :> c :> End) = (a,b,c)

-- fromTriple (a,b,c) = a :> b :> c :> End 

-- fixs :: forall ts a arg exp r. Proxy ts ->
--         (FromList a exp ts, FromList a (E arg exp) ts)
--         => ([exp a] -> [E arg exp a]) -> C arg exp r [E arg exp a]
-- fixs _ f = fmap (fromJust . appsToList) $ mrec (fromJust . appsFromList . f . appsToList')
--   where
--     fromJust (Just x) = x
--     fromJust _        = error "fromJust @ fixs: []"

--     appsToList' a = fromJust (appsToList (a :: Apps exp ts ))

-- fixfix :: (TypeList ts, TypeList ts', TypeList (Append ts ts')) => 
--           (Apps exp ts -> Apps exp ts' -> Apps (E arg exp) ts) -> 
--           (Apps exp ts -> Apps exp ts' -> Apps (E arg exp) ts') ->
--           C arg exp r (Apps (E arg exp) ts,  Apps (E arg exp) ts')
-- fixfix f1 f2 =
--   fmap splitApps $   
--   mrec (\z -> let (a,b) = splitApps z
--               in appendApps (f1 a b) (f2 a b))

  
hardcat :: FliPprE arg exp => E exp D -> E exp D -> E exp D
hardcat (E x) (E y) = E (fcat x y)

(<#>) :: FliPprE arg exp => E exp D -> E exp D -> E exp D
(<#>) = hardcat 

infixr 5 <#>

instance (D ~ t, FliPprE arg exp) => Semigroup (E exp t) where
  (<>) x y  = x `hardcat` (spaces `hardcat` y)

instance (D ~ t, FliPprE arg exp) => Monoid (E exp t) where
  mempty  = spaces -- ^ Notice that 'mempty' is not 'empty', as it is not a unit of (<>).
  mappend = (Data.Semigroup.<>) 

instance (D ~ t, FliPprE arg exp) => D.DocLike (E exp t) where
  text s = E (ftext s)
  empty  = E fempty 

  (<+>) x y = x `hardcat` text " " `hardcat` spaces `hardcat` y 

  line      = E fline
  linebreak = E flinebreak 

  align   = E . falign . unE
  nest k  = E . fnest k .  unE
  group   = E . fgroup . unE 


type FName = Int
type VName = Int 
type FCount = Int
type VCount = Int 

pprFName :: FName -> D.Doc
pprFName n = D.text ("ppr" ++ show n)

pprVName :: VName -> D.Doc
pprVName n | n < length fancyNames = D.text [fancyNames !! n]
           | otherwise             = D.text ("x" ++ show n)
  where
    fancyNames = "xyzwsturabcdeijklmnpqv"


varArg :: VName -> Printing D.Doc a
varArg x = Printing $ \_ _ _ -> pprVName x

type Prec = Rational
newtype Printing d (t :: k) = Printing { unPrinting :: FCount -> VCount ->  Prec -> d }

data Assoc = AssocL | AssocR | NonAssoc 

opPrinter :: D.DocLike d =>  Assoc -> d -> Prec -> (Prec -> d) -> (Prec -> d) ->  Prec -> d
opPrinter a d opK pprx ppry k =
  parensIf (k > opK) $ pprx (opK + dx) D.<> d D.<> ppry (opK + dy) 
  where
    (dx, dy) = case a of
                 AssocL   -> (0, 1)
                 AssocR   -> (1, 0)
                 NonAssoc -> (1, 1)               

fromDoc :: D.Doc -> Printing D.Doc a
fromDoc d = Printing $ \_ _ _ -> d 

-- instance FliPprE (Printing D.Doc) (Printing D.Doc) where
--   fapp (Printing f) x = Printing $ \fn vn k -> 
--     let d1 = f fn vn 9
--         d2 = unPrinting x fn vn 10 
--     in D.parensIf (k > 9) $ D.group $ d1 D.<+> D.text "`app`" D.<+> d2

--   farg f = Printing $ \fn vn k -> 
--     let vn' = vn + 1 
--         d = unPrinting (f (varArg vn')) fn vn' 1
--     in parensIf (k > 1) $ D.group $ 
--        D.text "arg" D.<+> D.text "$" D.<+> (D.text "\\" D.<> (pprVName vn' D.<+> D.nest 2 (D.text "->" D.</> d)))

--   fcase x bs = Printing $ \fn vn k ->
--     let ds = map (pprBranch fn vn) bs
--     in  parensIf (k > 9) $
--       D.text "case_" D.<+>
--       unPrinting x fn vn 10 D.</>
--       D.nest 2 (D.group (D.text "[" D.<> D.align (D.punctuate (D.text "," D.<> D.line) ds D.<> D.text "]")))
--       where
--         pprBranch fn vn (Branch (PInv s _ _) f) = 
--           let d = unPrinting (f (varArg (vn+1))) fn (vn+1) 0
--           in D.text s D.<+>
--              D.text "`Branch`" D.<+> D.align (D.text "\\" D.<> pprVName (vn+1) D.<+> D.text "->" D.<+> d)

--   funpair x f = Printing $ \fn vn k -> 
--     let d = unPrinting (f (varArg (vn+1)) (varArg (vn+2))) fn (vn+2) 0
--     in parensIf (k > 1) $
--        D.text "unpair" D.<+> unPrinting x fn vn 10 D.<+> 
--        D.text "$" D.<+> D.text "\\" D.<> pprVName (vn+1) D.<+> pprVName (vn+2) D.<+> D.text "->" D.<>
--        D.nest 2 (D.line D.<> d)
     
--   ftext s = Printing $ \_fn _vn k -> 
--     parensIf (k > 9) $
--     D.text "text" D.<+> D.ppr s

--   fcat x y = Printing $ \fn vn k ->
--     let d1 = unPrinting x fn vn 5
--         d2 = unPrinting y fn vn 5
--     in parensIf (k > 5) $
--        d1 D.<+> D.text "<#>" D.<+> d2

--   fbchoice x y = Printing $ \fn vn k -> 
--     let d1 = unPrinting x fn vn 4 
--         d2 = unPrinting y fn vn 4 
--     in parensIf (k > 4) $
--        D.align d1 D.<> D.line D.<> D.text "<?" D.<+> d2 

--   fempty = fromDoc (D.text "empty")
--   fline  = fromDoc (D.text "line")
--   flinebreak = fromDoc (D.text "linebreak")

--   fspace  = fromDoc (D.text "space")
--   fspaces = fromDoc (D.text "spaces")


--   falign e = Printing $ \fn vn k -> 
--     let d = unPrinting e fn vn 10
--     in parensIf (k > 9) $ D.text "align" D.<+> D.align d 

--   fgroup e = Printing $ \fn vn k -> 
--     let d = unPrinting e fn vn 10
--     in parensIf (k > 9) $ D.align (D.text "group" D.<> D.nest 2 (D.line D.<> D.align d ))

--   fnest i e = Printing $ \fn vn k -> 
--     let d = unPrinting e fn vn 10
--     in parensIf (k > 9) $ D.text "nest" D.<+> D.ppr i D.<+> D.align d 


data Printer s a = Printer (VCount -> Prec -> PrinterM s Doc)
                 | Pointer (Ref s ())

runPrinter :: Printer s a -> VCount -> Prec -> PrinterM s Doc
runPrinter (Printer f) vn k = f vn k
runPrinter (Pointer p) _  _ = return $ pprRef p

pprRef :: Ref s a -> Doc 
pprRef ref = D.text ("ppr" ++ show (refID ref))
                 
newtype PrinterM s a = PrinterM { runPrinterM :: ReaderT [Ref s (M.Map (Ref s ()) (PrinterM s Doc))] (RefM s) a } 
  deriving (Functor, Applicative, Monad, MonadFix)

instance MonadRef s (PrinterM s) where
  newRef a     = PrinterM $ newRef a
  readRef r    = PrinterM $ readRef r
  writeRef r a = PrinterM $ writeRef r a 

instance MonadReader [Ref s (M.Map (Ref s ()) (PrinterM s Doc))] (PrinterM s) where
  ask = PrinterM $ ask
  local f (PrinterM m) = PrinterM $ RM.local f m 

toPrinter :: Doc -> Printer s a
toPrinter d = Printer $ \_ _ -> return d 

instance FliPprE (Printer s) (Printer s) where
  farg f = Printer $ \vn k -> do
    df <- runPrinter (f (toPrinter $ pprVName vn)) (vn+1) 0
    return $ D.group $ D.nest 2 $ parensIf (k > 0) $ D.text "\\" <> pprVName vn <+> D.text "->" </> df

  fapp f a = Printer $ \vn k -> do 
    df <- runPrinter f vn 9
    da <- runPrinter a vn 10
    return $ parensIf (k > 9) $ df <+> da

  fcase a bs = Printer $ \vn k -> do 
    da <- runPrinter a vn 10
    ds <- mapM (\(Branch (PInv s _ _) f) -> do 
                     df <- runPrinter (f (toPrinter $ pprVName vn)) (vn+1) 0
                     return $ D.group $ D.nest 2 $ D.text s <+> D.text "$" <+> D.text "\\" <> pprVName vn <+> D.text "->" <+> df) bs 
    return $ parensIf (k > 9) $ D.group $ 
        D.text "case_" <+> da <+> 
          D.text "[" <> D.align (foldDoc (\x y -> x <> D.text "," </> y) ds <> D.text "]")
  
  funpair a f = Printer $ \vn k -> do
      da <- runPrinter a vn 10
      let dx = pprVName vn
      let dy = pprVName (vn + 1)
      db <- runPrinter (f (toPrinter dx) (toPrinter dy)) (vn+2) 0
      return $ parensIf (k > 0) $ D.align $ D.group $ 
         D.text "let" <+> parens (dx <> D.text "," <+> dy) <+> D.text "=" <+> D.align da </>
         D.text "in"  <+> D.align db

  ftext s = Printer $ \_ k -> 
    return $ parensIf (k > 9) $ D.text "text" <+> D.text (show s)

  fcat a b = Printer $ \vn k -> do
    da <- runPrinter a vn 5
    db <- runPrinter b vn 5
    return $ parensIf (k > 5) $ D.group $ da </> D.text "<#>" <+> db
    
  fbchoice a b = Printer $ \vn k -> do 
    da <- runPrinter a vn 4
    db <- runPrinter b vn 4
    return $ parensIf (k > 4) $ D.group $ da </> D.text "<?" <+> db

  fempty = toPrinter $ D.text "empty"
  fline  = toPrinter $ D.text "line"
  flinebreak = toPrinter $ D.text "linebreak"

  fspace  = toPrinter $ D.text "space"
  fspaces = toPrinter $ D.text "spaces"

  fgroup a = Printer $ \vn k -> do
    da <- runPrinter a vn 10
    return $ parensIf (k > 9) $ D.text "group" <+> da

  falign a = Printer $ \vn k -> do
    da <- runPrinter a vn 10
    return $ parensIf (k > 9) $ D.text "align" <+> da

  fnest n a = Printer $ \vn k -> do
    da <- runPrinter a vn 10
    return $ parensIf (k > 9) $ D.text "nest" <+> ppr n <+> da

instance FliPprD (PrinterM s) (Printer s) (Printer s) where
  fshare e = do
    let md = runPrinter e 0 0 
    (tbRef:_) <- ask
    r <- newRef $ ()
    modifyRef tbRef (M.insert r md)
    return $ Pointer $ r 

      

  flocal m = Printer $ \vn k -> do 
    tbRef <- newRef $ M.empty
    d <- RM.local (tbRef:) $ m >>= \e -> runPrinter e vn 0
    list <- M.toList <$> readRef tbRef
    defs <- D.group . D.align . (D.text "rec" <+>) . 
          D.foldDoc (\x y -> x </> D.text "and" <+> y) <$>
          mapM (\(ref, mdef) -> do
                   def <- mdef 
                   return $ D.group $ D.align (pprRef ref <+> D.nest 2 (D.text "=" </> def))) list
    return $ parensIf (k > 0) $ D.align $ 
      D.text "let" <+> D.align defs </>
      D.text "in" <+> d 


pprFliPpr :: PrinterM s (Printer s (t :: FType)) -> Prec -> RefM s Doc
pprFliPpr m k =
  runReaderT (runPrinterM $ runPrinter (flocal m) 0 k) []

instance D.Pretty (FliPpr t) where
  pprPrec k (FliPpr m) = runRefM (pprFliPpr m k) 

instance Show (FliPpr t) where
  show = show . ppr 
    
    

-- data Rep s a where
--   RArg    :: (a -> Rep s a) -> Rep s a
--   RApp    :: Rep s a -> Rep s a -> Rep s a 
--   RVar    :: a -> Rep s a 
--   RCase   :: Rep s a -> [(String, a -> Rep s a)] -> Rep s a
--   RUnPair :: Rep s a -> (a -> a -> Rep s a) -> Rep s a 
--   RText   :: String -> Rep s a
--   RChoice :: Rep s a -> Rep s a -> Rep s a
--   RCat    :: Rep s a -> Rep s a -> Rep s a
--   REmpty  :: Rep s a
--   RLine   :: Rep s a
--   RBreak  :: Rep s a
--   RSpace  :: Rep s a
--   RSpaces :: Rep s a
--   RAlign  :: Rep s a -> Rep s a
--   RGroup  :: Rep s a -> Rep s a
--   RNest   :: Int -> Rep s a -> Rep s a 
--   RLoc    :: Ref s (Rep s a) -> Rep s a 
--   RLocal  :: RefM s (Rep s a) -> Rep s a 

-- instance FliPprE (Const (Rep s a)) (Const (Rep s a)) where
--   fapp (Const f) (Const a) = Const (RApp f a)
--   farg f = Const $ RArg $ \a -> getConst $ f (Const $ RVar a)
  
--   fcase (Const a) bs = Const $ RCase a (map conv bs)
--     where
--       conv (Branch (PInv s _ _) f) =
--         (s, \a -> getConst $ f (Const $ RVar a))

--   funpair (Const a) f =
--     Const $ RUnPair a (\a b -> getConst $ f (Const $ RVar a) (Const $ RVar b))

  
--   fbchoice (Const a) (Const b) = Const (RChoice a b)
--   ftext s = Const (RText s)
--   fcat (Const a) (Const b) = Const (RCat a b)
--   fempty = Const REmpty
--   fline  = Const RLine
--   flinebreak = Const RBreak

--   fspace  = Const RSpace
--   fspaces = Const RSpaces

--   falign (Const a) = Const (RAlign a)
--   fgroup (Const a) = Const (RGroup a)
--   fnest n (Const a) = Const (RNest n a) 

-- instance FliPprD (RefM s) (Const (Rep s a)) (Const (Rep s a)) where
--   fshare e = do 
--     ref <- newRef (getConst e) 
--     return $ Const $ RLoc ref

--   flocal m = Const $ RLocal (getConst <$> m)

-- pprRep :: Rep s D.Doc -> RefM s D.Doc
-- pprRep rep = do
--   tbRef <- newRef $ M.empty 
--   v <- runReaderT (go rep 0 0) tbRef
--   tb <- readRef tbRef 
--   let ts = M.toList tb 
--   return $
--     D.text "do rec"
--     <+> D.align (vsep $ map (\(ref, def) ->
--                                pprRef ref  <+> D.text "=" <+> D.align def) ts)
--     $$ D.text "return" D.<+> v 
--   where
--     go :: Rep s D.Doc -> VCount -> Prec
--           -> ReaderT (Ref s (M.Map (Ref s (Rep s D.Doc)) D.Doc)) (RefM s) D.Doc
--     go (RArg f) vn k = do 
--       d <- go (f (pprVName vn)) (vn+1) k
--       return $ D.text "\\" <> pprVName vn <+> D.text "->" <+> D.align d

--     go (RApp f a) vn k = do
--       df <- go f vn 9
--       da <- go a vn 10
--       return $ parensIf (k > 9) $ df <+> da

--     go (RVar a) _ _ = return a
    
--     go (RCase a bs) vn k = do 
--       da <- go a vn 10
--       ds <- mapM (\(s,f) -> do 
--                      df <- go (f (pprVName vn)) (vn+1) 0
--                      return $ D.text s <+> D.text "$" <+> D.text "\\" <> pprVName vn <+> D.text "->" <+> D.align df) bs 
--       return $ parensIf (k > 9) $
--         D.text "case_" <+> da <+> 
--           D.text "[" <> D.align (foldDoc (\x y -> x <> D.text "," </> y) ds <> D.text "]")

--     go (RUnPair a f) vn k = do
--       da <- go a vn 10
--       let dx = pprVName vn
--       let dy = pprVName (vn + 1)
--       db <- go (f dx dy) (vn+2) 0
--       return $ parensIf (k > 0) $ D.align $ D.group $ 
--          D.text "let" <+> parens (dx <> D.text "," <+> dy) <+> D.text "=" <+> D.align da </>
--          D.text "in"  <+> D.align db

--     go (RText s) _ k = 
--       return $ parensIf (k > 9) $ D.text "text" <+> D.text (show s)

--     go (RCat a b) vn k = do
--       da <- go a vn 9
--       db <- go b vn 9
--       return $ parensIf (k > 9) $ da <+> D.text "`hardcat`" <+> db

--     go (RChoice a b) vn k = do
--       da <- go a vn 4
--       db <- go b vn 4
--       return $ parensIf (k > 4) $ D.group $ da </> D.text "<?" <+> db


--     go REmpty  _ _ = return $ D.text "empty"
--     go RLine   _ _ = return $ D.text "line"
--     go RBreak  _ _ = return $ D.text "linebreak"
--     go RSpace  _ _ = return $ D.text "space"
--     go RSpaces _ _ = return $ D.text "spaces"

--     go (RGroup a) vn k = do
--       da <- go a vn 10
--       return $ parensIf (k > 10) $ D.text "group" <+> da

--     go (RAlign a) vn k = do
--       da <- go a vn 10
--       return $ parensIf (k > 10) $ D.text "align" <+> da

--     go (RNest n a) vn k = do
--       da <- go a vn 10
--       return $ parensIf (k > 10) $ D.text "nest" <+> D.text (show n) <+> da 
    
      
--     go (RLoc ref) _ _ = do
--       tbRef <- ask
--       tb <- readRef tbRef 
--       case M.lookup ref tb of
--         Just _  -> return $ pprRef ref 
--         Nothing -> do
--           modifyRef tbRef (M.insert ref D.empty)
--           e <- readRef ref
--           d <- go e 0 0
--           modifyRef tbRef (M.insert ref d)
--           return $ pprRef ref

--     go (RLocal m) vn k = do
--       tbRef' <- newRef M.empty
--       e <- lift m
--       d <- RM.local tbRef' $ go e vn 0 
      

--     pprRef ref = D.text ("ppr" ++ show (refID ref))
          
      

                                                
    
  

-- instance FliPprD (ST s) (Printing D.Doc) (Printing D.Doc) where
--   fshare = Share



  
  -- ffix :: forall f. Container2 f =>
  --         f (Rec f (Printing D.Doc)) -> C (Printing D.Doc) (f (Printing D.Doc))
  -- ffix defs = CPS $ \cont -> Printing $ \fn vn k ->
  --   let fn' = length2 defs + fn
  --       fs  = evalState
  --               (traverse2 (const $ state $ \i -> (Printing $ \_ _ _ -> pprFName i, i+1)) defs)
  --               fn
  --       ns  = fold2 (\p -> [unPrinting p fn' vn 0])             fs
  --       ds  = fold2 (\a -> [unPrinting (pprDef fs a) fn' vn 0]) defs
  --   in parensIf (k > 0) $ D.align $ 
  --      D.align (D.text "letrec" D.<+>
  --               trav (zipWith (\a b -> a D.<+> D.text "=" D.<+> D.align b) ns ds)
  --              )
  --      D.</>
  --      D.text "in" D.<+> D.align (unPrinting (cont fs) fn' vn 0)
  --   where
  --     pprDef fs (Rec f) = f fs

  --     trav []  = D.empty
  --     trav [d] = d
  --     trav (d:ds) = d D.</> D.text "   and" D.<+> trav ds

  -- flet :: Printing D.Doc a -> C (Printing D.Doc) (Printing D.Doc a)
  -- flet a = CPS $ \cont -> Printing $ \fn vn k ->
  --   let fn' = fn + 1
  --       v   = Printing $ \_ _ _ -> pprFName fn
  --   in parensIf (k > 0) $ D.align $ 
  --        D.align (D.text "let" D.<+>
  --                   pprFName fn D.<+> D.text "=" D.<+>
  --                    D.align (unPrinting a fn' vn 0))         
  --        D.</>
  --        D.text "in" D.<+> D.align (unPrinting (cont v) fn' vn 0)
      
  


-- instance (exp ~ Printing D.Doc) => D.Pretty (E exp t) where
--   pprPrec k e = unPrinting (unE e) 0 0 k 


-- instance D.Pretty (FliPpr t) where
--   pprPrec k (FliPpr e) = unPrinting e 0 0 k

-- instance Show (FliPpr t) where
--   show = show . ppr 

example1 :: FliPpr ([Bool] :~> D)
example1 = flippr $ do
  let manyParens d = local $ do
        rec m <- share $ d <? parens m
        return m

  pprTF <- share $ arg $ \i -> manyParens $ case_ i
    [ unTrue `Branch` \_ -> text "True",
      unFalse `Branch` \_ -> text "False" ]

  rec ppr <- share $ arg $ \x -> manyParens $ case_ x
              [ unNil `Branch` \_ -> text "[" <> text "]",
                unCons `Branch` \xx -> unpair xx $ \a x -> 
                  brackets (ppr' `app` a `app` x)]

      ppr' <- share $ arg $ \a -> arg $ \x -> case_ x
        [ unNil `Branch` \_ -> pprTF `app` a, 
          unCons `Branch` \xx -> 
                  unpair xx $ \b x -> 
                     pprTF `app` a <> text "," <> ppr' `app` b `app` x]
  return ppr
  where
    unTrue  = PInv "unTrue" (\x -> if x then Just () else Nothing) (const (Just True))
    unFalse = PInv "unFalse" (\x -> if x then Nothing else Just ()) (const (Just False))

    unNil = PInv "unNil" f g
      where
        f [] = Just ()
        f _  = Nothing
        g () = Just []
    unCons = PInv "unCons" f g
      where
        f [] = Nothing
        f (a:x) = Just (a,x)
        g (a,x) = Just (a:x) 
    


-- example1 :: FliPpr ([Bool] :~> D)
-- example1 = flippr $ do
--   let manyParens d = fix1 (\m -> d <? parens m)

--   pprTF <- share $ arg $ \i -> manyParens $ case_ i
--         [ unTrue  `Branch` \_ -> text "True",
--           unFalse `Branch` \_ -> text "False" ]

--   (ppr, _ppr') <- fix2 $ \(~(_ppr, ppr')) ->
--     let ppr_ = arg $ \x -> case_ x
--               [ unNil `Branch` \_ -> text "[" <> text "]",
--                 unCons `Branch` \xx -> unC $ do
--                   (a,x) <- unpair xx
--                   return $ brackets (ppr' `app` a `app` x)]
--         ppr'_ = arg $ \a -> arg $ \x -> case_ x
--           [ unNil `Branch` \_ -> pprTF `app` a
--               , unCons `Branch` \xx -> unC $ do
--                   (b,x) <- unpair xx
--                   return $ pprTF `app` a <> text "," <> ppr' `app` b `app` x]
--     in (ppr_, ppr'_)
--   return ppr 
--   where
--     unTrue  = PInv "unTrue" (\x -> if x then Just () else Nothing) (const (Just True))
--     unFalse = PInv "unFalse" (\x -> if x then Nothing else Just ()) (const (Just False))

--     unNil = PInv "unNil" f g
--       where
--         f [] = Just ()
--         f _  = Nothing
--         g () = Just []
--     unCons = PInv "unCons" f g
--       where
--         f [] = Nothing
--         f (a:x) = Just (a,x)
--         g (a,x) = Just (a:x) 
  
    
