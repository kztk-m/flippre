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

import qualified Data.Map as M

import Control.Monad.Reader hiding (local) 
import qualified Control.Monad.Reader as RM 

import Text.FliPpr.Doc as D

import Text.FliPpr.Internal.Ref


-- | A kind for datatypes in FliPpr. 
data FType = D | Type :~> FType 


type In a = (Typeable a, Eq a)

-- | A type for partial bijections. The 'String'-typed field will be used in pretty-printing
--   of FliPpr expressions. 
data a <-> b = PInv String (a -> Maybe b) (b -> Maybe a) 

-- | A datatype represents branches. 
data Branch arg exp a (t :: FType) =
  forall b. In b => Branch (a <-> b) (arg b -> exp t)

-- | A finally-tagless implementation of FliPpr expressions. 
--   The APIs are only for internal use. 
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

  fline'     :: exp D -- (fline `fbchoice` empty)
  fnespaces' :: exp D -- ((fspace `fcat` fspaces) `fbchoice` empty)

  falign :: exp D -> exp D
  fgroup :: exp D -> exp D
  fnest  :: Int -> exp D -> exp D

-- | A finally-tagless implementation of FliPpr expressions
--   that can contain recursive definictions.
--
--   Again, the APIs are only for intenral use.
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

-- | Make a closed FliPpr definition. A typical use is:
--
--   > flippr $ do
--   >   rec ppr <- share $ arg $ \i -> ...
--   >   return ppr

flippr :: (forall m arg exp. FliPprD m arg exp => m (E exp t)) -> FliPpr t
flippr x = FliPpr (unE <$> x) -- flipprPure (unC x)



-- | Indicating that there can be zero-or-more spaces in parsing.
--   In pretty-printing, it is equivalent to @text ""@. 
{-# INLINABLE spaces #-}
spaces :: FliPprE arg exp => E exp D
spaces = E fspaces 


-- | In pretty-printing, it works as @text " "@. In parsing
--   it behaves a single space in some sense. 
{-# INLINABLE space #-}
space :: FliPprE arg exp => E exp D
space = E fspace

-- | For internal use. Use '<+>'.
{-# INLINABLE nespaces #-}
nespaces :: FliPprE arg exp => E exp D
nespaces = space <#> spaces

-- | For internal use. Use '<+>.'.
{-# INLINABLE nespaces' #-}
nespaces' :: FliPprE arg exp => E exp D
nespaces' = E fnespaces' 

-- | Similar to 'line', but it also accepts the empty string in parsing.
{-# INLINABLE line' #-}
line' :: FliPprE arg exp => E exp D
line' = E fline' 

-- | A wrapper for 'farg'. 
{-# INLINABLE arg #-}
arg :: (In a, FliPprE arg exp) => (A arg a -> E exp t) -> E exp (a :~> t)
arg f = E (farg (coerce f))

-- | A wrapper for 'fapp'. 
{-# INLINABLE app #-}
app :: (In a, FliPprE arg exp) => E exp (a :~> t) -> A arg a -> E exp t 
app (E f) (A a) = E (fapp f a) 

-- | FliPpr version of '$'.
{-# INLINE (@@) #-}
(@@) :: (In a, FliPprE arg exp) => E exp (a :~> t) -> A arg a -> E exp t 
(@@) = app

infixr 0 @@

-- | case branching. 
{-# INLINABLE case_ #-}
case_ :: (In a, FliPprE arg exp) => A arg a -> [Branch (A arg) (E exp) a r] -> E exp r
case_ (A a) bs = E (fcase a (coerce bs))

-- | A CPS style conversion from @A arg (a,b)@ to a pair of @A arg a@ and @A arg b@.
--   A typical use of 'unpair' is to implement (invertible) pattern matching in FliPpr.
--
--   'Language.FliPpr.TH' provides 'un' and 'branch'. By using these functions,
--   one can avoid using a bit awkward 'unpair' explicitly. 
{-# INLINABLE unpair #-}
unpair :: (In a, In b, FliPprE arg exp) => A arg (a,b) -> (A arg a -> A arg b -> E exp r) -> E exp r
unpair (A x) k = E $ funpair x (coerce k)


-- | Biased choice. @a <? b = a@ in parsing, but it accepts strings indicated by both @a@ and @b$ in parsing.

(<?) :: FliPprE arg exp => E exp D -> E exp D -> E exp D
(<?) (E x) (E y) = E (fbchoice x y)

infixr 4 <?

-- | Knot-tying operator. To guarantee that we generate CFGs, every recursive function must be
--   defined via 'share'. Also, even for non-recursive function, 'share' ensures that its definition will be
--   shared instead of copied in parser construction. Thus, it is recommended that every function is defined
--   in the style of:
--
--   > func <- share $ arg $ \i -> ...
  
share :: FliPprD m arg exp => E exp t -> m (E exp t)
share e = E <$> fshare (unE e) 


-- | 'local' enables us to define recursive functions in the body of other functions. 
local :: FliPprD m arg exp => m (E exp t) -> E exp t
local m = E $ flocal (unE <$> m)
  
-- | Unlike '(<>)' that allows spaces between concatenated elementes in parsing,
--   'hardcat' does not allow such extra spaces in parsing. 
{-# INLINABLE hardcat #-}  
hardcat :: FliPprE arg exp => E exp D -> E exp D -> E exp D
hardcat (E x) (E y) = E (fcat x y)

-- | A better syntax for `hardcat`.

{-# INLINE (<#>) #-}
(<#>) :: FliPprE arg exp => E exp D -> E exp D -> E exp D
(<#>) = hardcat 

infixr 5 <#>

instance (D ~ t, FliPprE arg exp) => Semigroup (E exp t) where
  (<>) x y  = x `hardcat` (spaces `hardcat` y)

instance (D ~ t, FliPprE arg exp) => Monoid (E exp t) where
  mempty  = spaces -- Notice that 'mempty' is not 'empty', as it is not a unit of @(<>)@.
  mappend = (Data.Semigroup.<>) 

-- | We can use pretty-printing combinators defined in 'Text.FliPpr.Doc' also for FliPpr expressions. 
instance (D ~ t, FliPprE arg exp) => D.DocLike (E exp t) where
  text s = E (ftext s)
  empty  = E fempty 

  (<+>) x y = x `hardcat` text " " `hardcat` spaces `hardcat` y 

  line      = E fline
  linebreak = E flinebreak 

  align   = E . falign . unE
  nest k  = E . fnest k .  unE
  group   = E . fgroup . unE 


type VName = Int 
type VCount = Int 

pprVName :: VName -> D.Doc
pprVName n | n < length fancyNames = D.text [fancyNames !! n]
           | otherwise             = D.text ("x" ++ show n)
  where
    fancyNames = "xyzwsturabcdeijklmnpqv"

type Prec = Rational


data Printer s a = Printer (VCount -> Prec -> PrinterM s Doc)
                 | Pointer (Ref s ())

runPrinter :: Printer s a -> VCount -> Prec -> PrinterM s Doc
runPrinter (Printer f) vn k = f vn k
runPrinter (Pointer p) _  _ = return $ pprRef p

pprRef :: Ref s a -> Doc 
pprRef ref = D.text ("ppr" ++ show (refID ref))

-- FIXME: The current implementation does not track the number of free variables.

newtype PrinterM s a = PrinterM { runPrinterM :: ReaderT [Ref s (M.Map (Ref s ()) (PrinterM s Doc))] (RefM s) a } 
  deriving (Functor, Applicative, Monad, MonadFix)

instance MonadRef s (PrinterM s) where
  newRef a     = PrinterM $ newRef a
  readRef r    = PrinterM $ readRef r
  writeRef r a = PrinterM $ writeRef r a 

  newRawRef a = PrinterM $ newRawRef a
  readRawRef r = PrinterM $ readRawRef r
  writeRawRef r a = PrinterM $ writeRawRef r a 

instance MonadReader [Ref s (M.Map (Ref s ()) (PrinterM s Doc))] (PrinterM s) where
  ask = PrinterM $ ask
  local f (PrinterM m) = PrinterM $ RM.local f m 

toPrinter :: Doc -> Printer s a
toPrinter d = Printer $ \_ _ -> return d 

-- | An instance for pretty-printing FliPpr expressions themselves (not for pretty-printing interpretation).
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

  fline'     = toPrinter $ D.text "line'"
  fnespaces' = toPrinter $ D.text "nespaces'" 

  fgroup a = Printer $ \vn k -> do
    da <- runPrinter a vn 10
    return $ parensIf (k > 9) $ D.text "group" <+> da

  falign a = Printer $ \vn k -> do
    da <- runPrinter a vn 10
    return $ parensIf (k > 9) $ D.text "align" <+> da

  fnest n a = Printer $ \vn k -> do
    da <- runPrinter a vn 10
    return $ parensIf (k > 9) $ D.text "nest" <+> ppr n <+> da


-- | An instance for pretty-printing recursive defined FliPpr expressions. 
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


instance D.Pretty (FliPpr t) where
  pprPrec k (FliPpr m) = runRefM (pprFliPpr m k) 
    where
      pprFliPpr :: PrinterM s (Printer s (t :: FType)) -> Prec -> RefM s Doc
      pprFliPpr m k =
        runReaderT (runPrinterM $ runPrinter (flocal m) 0 k) []

instance Show (FliPpr t) where
  show = show . ppr 
    
