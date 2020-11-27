{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
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
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -fwarn-unused-imports -fwarn-incomplete-patterns #-}

module Text.FliPpr.Internal.Type
  ( FType (..),
    In,
    FliPprE (..),
    FliPprD,
    A (..),
    E (..),
    FliPpr (..),
    Branch (..),
    PartialBij (..),
    flippr,
    arg,
    app,
    (@@),
    case_,
    unpair,
    ununit,
    line',
    space,
    spaces,
    nespaces,
    nespaces',
    (<?),
    hardcat,
    (<#>),

    -- * Making recursive definitions
    module Defs,
  )
where

import Control.Applicative (Const (..))
import Control.Monad.Fail
import Control.Monad.Reader hiding (lift, local)
import Control.Monad.State hiding (lift)
import Data.Coerce (coerce)
import Data.Kind (Type)
import Data.Semigroup (Semigroup (..))
import Text.FliPpr.Doc as D
import Text.FliPpr.Internal.Defs as Defs

-- | A kind for datatypes in FliPpr.
data FType = D | Type :~> FType

type In a = Eq a

-- | A type for partial bijections. The 'String'-typed field will be used in pretty-printing
--   of FliPpr expressions.
data PartialBij a b = PartialBij String (a -> Maybe b) (b -> Maybe a)

-- | A datatype represents branches.
data Branch arg exp a (t :: FType)
  = forall b. In b => Branch (PartialBij a b) (arg b -> exp t)

-- | A finally-tagless implementation of FliPpr expressions.
--   The APIs are only for internal use.
class FliPprE (arg :: Type -> Type) (exp :: FType -> Type) | exp -> arg where
  fapp :: In a => exp (a :~> t) -> arg a -> exp t
  farg :: In a => (arg a -> exp t) -> exp (a :~> t)

  fcase :: In a => arg a -> [Branch arg exp a t] -> exp t

  funpair :: (In a, In b) => arg (a, b) -> (arg a -> arg b -> exp t) -> exp t
  fununit :: arg () -> exp t -> exp t

  fbchoice :: exp D -> exp D -> exp D

  ftext :: String -> exp D
  fempty :: exp D
  fcat :: exp D -> exp D -> exp D

  -- For optimization purpose.
  fspace :: exp D
  fspaces :: exp D

  fline :: exp D -- translated to @text " " <> spaces@ in parsing
  flinebreak :: exp D -- translated to @spaces@ in parsing

  fline' :: exp D -- (fline `fbchoice` empty)
  fnespaces' :: exp D -- ((fspace `fcat` fspaces) `fbchoice` empty)

  falign :: exp D -> exp D
  fgroup :: exp D -> exp D
  fnest :: Int -> exp D -> exp D

type FliPprD arg exp = (Defs exp, FliPprE arg exp)

-- -- | A finally-tagless implementation of FliPpr expressions
-- --   that can contain recursive definictions.
-- --
-- --   Again, the APIs are only for intenral use.
-- class (FliPprE arg exp, MonadFix m) => FliPprD m arg exp | exp -> arg, exp -> m where
--   -- Using ffix to define a recursion would not be a good idea.
--   -- The information is used to define a grammar generation that is
--   -- to be used in "parsing" evaluation.
--   --
--   -- To use Earley or Frost's parser combinators it suffices to mark
--   -- body of recursive functions. This is much more convient as
--   -- we can use grammars via recursive do notations.
--   --
--   -- If such a "marking" approach would suffice for some other grammar manipulations such
--   -- as left recursion elimination or injectivity analysis, first character extraction and so on.
--   -- Then, we will use "marking" approach instead of "ffix".
--   --
--   -- By 2017-11-18 kztk:
--   -- It turns out that "marking" approach is not useful to define local definitions.
--   -- The local defintions are specially important for FliPpr, as we can
--   -- define ``inlinable'' functions. A typical example is @manyParens@, a
--   -- function to annotate a position to which arbitrary number of parens can be
--   -- placed around. By @ffix@, such a function is easy to define.
--   --
--   -- @
--   -- manyParens :: FliPpr arg exp => exp D -> exp D
--   -- manyParens d = ffix (\x -> d <|> parens x)
--   -- @
--   --
--   -- However, this is hard to achieve by using the "marking" approach, as
--   -- it can only define global definitions.
--   --
--   -- Thus, we many need both or use "marking" as a compromised alternative syntax.
--   -- It seems to me that we cannot directly converted it to @ffix@ with using
--   -- some compromising (Data.Dynamic, for example).
--   --
--   -- Anyway, @ffix@ is more general, and due to free variables, we cannot convert
--   -- it to "marking" in general. Let's have both at this level.
--   --
--   -- By kztk @ 2017-11-25
--   --
--   -- It seems to me that it is not that straightforward to define the semantics of
--   -- marking. Making a definition complex would be a not a good idea, and
--   -- mutual recursions that are hard to define by 'ffix' would not appear so oftenly.
--   --
--   -- Tentatively, we removed the marking function.
--   --
--   -- By kztk @ 2017-11-26
--   -- Having single recursion unbearablely slow and not useful at all.
--   -- The above description was wrong, and the following definition would suffice.
--   --
--   -- @
--   -- manyParens d = local $ do rec r <- rule $ d <? parens r
--   --                           return r
--   -- @
--   --
--   --
--   -- By kztk @ 2017-11-26
--   -- I find that using @rule@ has a problem on pretty-printing interpretation.
--   -- Thus, I revisited usual ffix. We cannot avoid considering general mutual
--   -- recursions as below.
--   --
--   -- ffix  :: (exp t -> exp t) -> exp t
--   --
--   --
--   -- By kztk @ 2017-12-22
--   -- Changed its type from Oleg's comment.
--   --
--   -- ffix :: Container2 f => f (Rec f exp) -> CPS exp (f exp)
--   -- flet :: exp t -> CPS exp (exp t)
--   -- flet = return
--   --
--   -- By kztk @ 2018-01-01
--   --
--   -- Changed its type to
--   fshare :: exp t -> m (exp t)
--   flocal :: m (exp t) -> exp t

-- | 'A arg a' is nothing but @arg a@, but used for controlling type inference.
newtype A arg a = A {unA :: arg a}

-- | Similarly, 'E exp t' is nothing but @exp t@.
newtype E exp t = E {unE :: exp t}

newtype FliPpr t = FliPpr (forall arg exp. FliPprD arg exp => exp t)

-- flipprPure :: (forall arg exp. FliPprD arg exp => E exp t) -> FliPpr t
-- flipprPure x = FliPpr (unE x)

-- | Make a closed FliPpr definition. A typical use is:
--
--   > flippr $ do
--   >   rec ppr <- share $ arg $ \i -> ...
--   >   return ppr
flippr :: (forall arg exp. FliPprD arg exp => E exp t) -> FliPpr t
flippr x = FliPpr (unE x) -- flipprPure (unC x)

-- | Indicating that there can be zero-or-more spaces in parsing.
--   In pretty-printing, it is equivalent to @text ""@.
{-# INLINEABLE spaces #-}
spaces :: FliPprE arg exp => E exp D
spaces = E fspaces

-- | In pretty-printing, it works as @text " "@. In parsing
--   it behaves a single space in some sense.
{-# INLINEABLE space #-}
space :: FliPprE arg exp => E exp D
space = E fspace

-- | For internal use. Use '<+>'.
{-# INLINEABLE nespaces #-}
nespaces :: FliPprE arg exp => E exp D
nespaces = space <#> spaces

-- | For internal use. Use '<+>.'.
{-# INLINEABLE nespaces' #-}
nespaces' :: FliPprE arg exp => E exp D
nespaces' = E fnespaces'

-- | Similar to 'line', but it also accepts the empty string in parsing.
{-# INLINEABLE line' #-}
line' :: FliPprE arg exp => E exp D
line' = E fline'

-- | A wrapper for 'farg'.
{-# INLINEABLE arg #-}
arg :: (In a, FliPprE arg exp) => (A arg a -> E exp t) -> E exp (a :~> t)
arg f = E (farg (coerce f))

-- | A wrapper for 'fapp'.
{-# INLINEABLE app #-}
app :: (In a, FliPprE arg exp) => E exp (a :~> t) -> A arg a -> E exp t
app (E f) (A a) = E (fapp f a)

-- | FliPpr version of '$'.
{-# INLINE (@@) #-}
(@@) :: (In a, FliPprE arg exp) => E exp (a :~> t) -> A arg a -> E exp t
(@@) = app

infixr 0 @@

-- | case branching.
{-# INLINEABLE case_ #-}
case_ :: (In a, FliPprE arg exp) => A arg a -> [Branch (A arg) (E exp) a r] -> E exp r
case_ (A a) bs = E (fcase a (coerce bs))

-- | A CPS style conversion from @A arg (a,b)@ to a pair of @A arg a@ and @A arg b@.
--   A typical use of 'unpair' is to implement (invertible) pattern matching in FliPpr.
--
--   'Language.FliPpr.TH' provides 'un' and 'branch'. By using these functions,
--   one can avoid using a bit awkward 'unpair' explicitly.
{-# INLINEABLE unpair #-}
unpair :: (In a, In b, FliPprE arg exp) => A arg (a, b) -> (A arg a -> A arg b -> E exp r) -> E exp r
unpair (A x) k = E $ funpair x (coerce k)

{-# INLINEABLE ununit #-}
ununit :: FliPprE arg exp => A arg () -> E exp r -> E exp r
ununit (A x) y = E $ fununit x (coerce y)

-- | Biased choice. @a <? b = a@ in parsing, but it accepts strings indicated by both @a@ and @b$ in parsing.
(<?) :: FliPprE arg exp => E exp D -> E exp D -> E exp D
(<?) (E x) (E y) = E (fbchoice x y)

instance Defs e => Defs (E e) where
  newtype Rules (E e) a = RE (Rules e a)

  lift (E x) = RE (lift x)
  unlift (RE x) = E (unlift x)

  pairRules (RE r1) (RE r2) = RE (pairRules r1 r2)

  unpairRules (RE e) k = RE $ unpairRules e (coerce k)

  letr h = RE $ letr (coerce h)

infixr 4 <?

instance Defs exp => Convertible exp (T a) (E exp a) where
  fromRules = return . E . unlift
  toRules = lift . unE

-- -- | Knot-tying operator. To guarantee that we generate CFGs, every recursive function must be
-- --   defined via 'share'. Also, even for non-recursive function, 'share' ensures that its definition will be
-- --   shared instead of copied in parser construction. Thus, it is recommended that every function is defined
-- --   in the style of:
-- --
-- --   > func <- share $ arg $ \i -> ...
-- share :: FliPprD m arg exp => E exp t -> m (E exp t)
-- share e = E <$> fshare (unE e)

-- -- | 'local' enables us to define recursive functions in the body of other functions.
-- local :: FliPprD m arg exp => m (E exp t) -> E exp t
-- local m = E $ flocal (unE <$> m)

-- | Unlike '(<>)' that allows spaces between concatenated elementes in parsing,
--   'hardcat' does not allow such extra spaces in parsing.
{-# INLINEABLE hardcat #-}
hardcat :: FliPprE arg exp => E exp D -> E exp D -> E exp D
hardcat (E x) (E y) = E (fcat x y)

-- | A better syntax for `hardcat`.
{-# INLINE (<#>) #-}
(<#>) :: FliPprE arg exp => E exp D -> E exp D -> E exp D
(<#>) = hardcat

infixr 5 <#>

instance (D ~ t, FliPprE arg exp) => Semigroup (E exp t) where
  (<>) x y = x `hardcat` (spaces `hardcat` y)

-- FIXME: This instance does not satisify the laws. Maybe, we should remove Monoid from the
-- superclass of DocLike.
instance (D ~ t, FliPprE arg exp) => Monoid (E exp t) where
  mempty = spaces
  mappend = (Data.Semigroup.<>)

-- | We can use pretty-printing combinators defined in 'Text.FliPpr.Doc' also for FliPpr expressions.
instance (D ~ t, FliPprE arg exp) => D.DocLike (E exp t) where
  text s = E (ftext s)
  empty = E fempty

  (<+>) x y = x `hardcat` text " " `hardcat` spaces `hardcat` y

  line = E fline
  linebreak = E flinebreak

  align = E . falign . unE
  nest k = E . fnest k . unE
  group = E . fgroup . unE

-- Pretty printing interpretation of FliPprD for convenience, it is a sort of
-- unembedding but we use untyped variants.

newtype RName = RName Int deriving (Num, Show, Enum)

newtype IName = IName Int deriving (Num, Show, Enum)

type Prec = Int -- precedence

newtype PrinterI (a :: FType) = PrinterI {runPrinterI :: Prec -> State (RName, IName) D.Doc}

newIName :: State (RName, IName) IName
newIName = do
  (i, v) <- get
  let !v' = v + 1
  put (i, v')
  return v

newRName :: State (RName, IName) RName
newRName = do
  (i, v) <- get
  let !i' = i + 1
  put (i', v)
  return i

pprIName :: IName -> D.Doc
pprIName n
  | coerce n < length fancyNames = D.text [fancyNames !! coerce n]
  | otherwise = D.text ("x" ++ show n)
  where
    fancyNames = "xyzwsturabcdeijklmnpqv"

pprRName :: RName -> D.Doc
pprRName n = D.text ("f" ++ show n)

instance FliPprE (Const IName) PrinterI where
  fapp e1 e2 = PrinterI $ \k -> do
    d1 <- runPrinterI e1 9
    let d2 = pprIName (getConst e2)
    return $ D.parensIf (k > 9) $ d1 D.<+> d2

  farg h = PrinterI $ \k -> do
    x <- newIName
    d <- runPrinterI (h $ Const x) 0
    return $ D.parensIf (k > 0) $ D.text "\\" <> pprIName x <+> D.text "->" </> d

  fcase a bs = PrinterI $ \k -> do
    let da = pprIName $ getConst a
    ds <- forM bs $ \(Branch (PartialBij s _ _) f) -> do
      x <- newIName
      df <- runPrinterI (f $ Const x) 0
      return $ D.group $ D.nest 2 $ D.text s <+> D.text "$" <+> D.text "\\" <> pprIName x <+> D.text "->" <+> df
    return $
      parensIf (k > 9) $
        D.group $
          D.text "case_" <+> da
            <+> D.text "[" <> D.align (foldDoc (\x y -> x <> D.text "," </> y) ds <> D.text "]")

  funpair a f = PrinterI $ \k -> do
    let da = pprIName (getConst a)
    x <- newIName
    y <- newIName
    db <- runPrinterI (f (Const x) (Const y)) 0
    return $
      parensIf (k > 0) $
        D.align $
          D.group $
            D.text "let" <+> parens (pprIName x <> D.text "," <+> pprIName y) <+> D.text "=" <+> D.align da
              </> D.text "in" <+> D.align db

  fununit a e = PrinterI $ \k -> do
    let da = pprIName (getConst a)
    de <- runPrinterI e 0
    return $
      D.parensIf (k > 0) $
        D.align $
          D.group $
            D.text "let () =" <+> D.align da
              </> D.text "in" <+> D.align de

  ftext s = PrinterI $ \k ->
    return $ parensIf (k > 9) $ D.text "text" <+> D.text (show s)

  fcat a b = PrinterI $ \k -> do
    da <- runPrinterI a 5
    db <- runPrinterI b 5
    return $ parensIf (k > 5) $ D.group $ da </> D.text "<#>" <+> db

  fbchoice a b = PrinterI $ \k -> do
    da <- runPrinterI a 4
    db <- runPrinterI b 4
    return $ parensIf (k > 4) $ D.group $ da </> D.text "<?" <+> db

  fempty = PrinterI $ const $ return $ D.text "empty"
  fline = PrinterI $ const $ return $ D.text "line"
  flinebreak = PrinterI $ const $ return $ D.text "linebreak"

  fspace = PrinterI $ const $ return $ D.text "space"
  fspaces = PrinterI $ const $ return $ D.text "spaces"

  fline' = PrinterI $ const $ return $ D.text "line'"
  fnespaces' = PrinterI $ const $ return $ D.text "nespaces'"

  fgroup a = PrinterI $ \k -> do
    da <- runPrinterI a 10
    return $ parensIf (k > 9) $ D.text "group" <+> da

  falign a = PrinterI $ \k -> do
    da <- runPrinterI a 10
    return $ parensIf (k > 9) $ D.text "align" <+> da

  fnest n a = PrinterI $ \k -> do
    da <- runPrinterI a 10
    return $ parensIf (k > 9) $ D.text "nest" <+> ppr n <+> da

data RPairD = RPairD D.Doc D.Doc | ROtherD D.Doc

pprRPairD :: RPairD -> D.Doc
pprRPairD (RPairD d1 d2) = D.hcat [D.text "<", d1, D.text ",", d2, D.text ">"]
pprRPairD (ROtherD d) = d

instance Defs PrinterI where
  newtype Rules PrinterI _a = PRules {runPRules :: Prec -> State (RName, IName) RPairD}

  lift a = PRules $ \k -> do
    d <- runPrinterI a 10
    return $ ROtherD $ parensIf (k > 9) $ D.text "↑" D.<> d

  unlift r = PrinterI $ \k -> do
    d <- pprRPairD <$> runPRules r 10
    return $ parensIf (k > 9) $ D.text "↓" D.<> d

  pairRules r1 r2 = PRules $ \_ -> do
    d1 <- pprRPairD <$> runPRules r1 0
    d2 <- pprRPairD <$> runPRules r2 0
    return $ RPairD d1 d2

  unpairRules m f = PRules $ \k -> do
    d <- pprRPairD <$> runPRules m 0
    x <- newRName
    y <- newRName
    dr <- pprRPairD <$> runPRules (f (PRules $ const $ return $ ROtherD $ pprRName x) (PRules $ const $ return $ ROtherD $ pprRName y)) 0
    return $
      ROtherD $
        parensIf (k > 0) $
          D.align $
            D.group $
              D.text "let" <+> parens (pprRName x <> D.text "," <+> pprRName y) <+> D.text "=" <+> D.align d <+> D.text "in"
                </> D.align dr

  letr f = PRules $ \k -> do
    x <- newRName
    res <- runPRules (f (PrinterI $ \_ -> return $ pprRName x)) 0
    return $
      ROtherD $
        parensIf (k > 0) $ case res of
          RPairD d1 d2 ->
            D.align $
              D.group $
                D.text "let rec" <+> pprRName x <+> D.text "=" <+> d1 <+> D.text "in"
                  </> D.align d2
          ROtherD d ->
            D.align $ D.group $ D.text "letr" <+> pprRName x <> D.text "." </> D.nest 2 (D.align d)

instance D.Pretty (FliPpr t) where
  pprPrec _ (FliPpr m) = evalState (runPrinterI m 0) (0, 0)

-- type RName = Int

-- type VCount = Int

-- pprVName :: RName -> D.Doc
-- pprVName n
--   | n < length fancyNames = D.text [fancyNames !! n]
--   | otherwise = D.text ("x" ++ show n)
--   where
--     fancyNames = "xyzwsturabcdeijklmnpqv"

-- type Prec = Rational

-- data Printer s a
--   = Printer (VCount -> Prec -> PrinterM s Doc)
--   | Pointer (Ref s ())

-- runPrinterI ::inter s a -> VCount -> Prec -> PrinterM s Doc
-- runPrinterI (Pter f) vn k = f vn k
-- runPrinterI (Pter p) _ _ = return $ pprRef p

-- pprRef :: Ref s a -> Doc
-- pprRef ref = D.text ("ppr" ++ show (refID ref))

-- -- FIXME: The current implementation does not track the number of free variables.

-- newtype PrinterM s a = PrinterM {runPrinterM :: ReaderT [Ref s (M.Map (Ref s ()) (PrinterM s Doc))] (RefM s) a}
--   deriving (Functor, Applicative, Monad, MonadFix, MonadFail)

-- instance MonadRef s (PrinterM s) where
--   newRef a = PrinterM $ newRef a
--   readRef r = PrinterM $ readRef r
--   writeRef r a = PrinterM $ writeRef r a

--   newRawRef a = PrinterM $ newRawRef a
--   readRawRef r = PrinterM $ readRawRef r
--   writeRawRef r a = PrinterM $ writeRawRef r a

-- instance MonadReader [Ref s (M.Map (Ref s ()) (PrinterM s Doc))] (PrinterM s) where
--   ask = PrinterM $ ask
--   local f (PrinterM m) = PrinterM $ RM.local f m

-- toPrinter :: Doc -> Printer s a
-- toPrinter d = Printer $ \_ _ -> return d

-- -- | An instance for pretty-printing FliPpr expressions themselves (not for pretty-printing interpretation).
-- instance FliPprE (Printer s) (Printer s) where
--   farg f = Printer $ \vn k -> do
--     df <- runPrinterI (foPrinter $ pprVName vn)) (vn + 1) 0
--     return $ D.group $ D.nest 2 $ parensIf (k > 0) $ D.text "\\" <> pprVName vn <+> D.text "->" </> df

--   fapp f a = Printer $ \vn k -> do
--     df <- runPrinterI f 9
--     da <- runPrinterI a 10
--     return $ parensIf (k > 9) $ df <+> da

--   fcase a bs = Printer $ \vn k -> do
--     da <- runPrinterI a 10
--     ds <-
--       mapM
--         ( \(Branch (PartialBij s _ _) f) -> do
--             df <- runPrinterI (foPrinter $ pprVName vn)) (vn + 1) 0
--             return $ D.group $ D.nest 2 $ D.text s <+> D.text "$" <+> D.text "\\" <> pprVName vn <+> D.text "->" <+> df
--         )
--         bs
--     return $
--       parensIf (k > 9) $
--         D.group $
--           D.text "case_" <+> da
--             <+> D.text "[" <> D.align (foldDoc (\x y -> x <> D.text "," </> y) ds <> D.text "]")

--   funpair a f = Printer $ \vn k -> do
--     da <- runPrinterI a 10
--     let dx = pprVName vn
--     let dy = pprVName (vn + 1)
--     db <- runPrinterI (foPrinter dx) (toPrinter dy)) (vn + 2) 0
--     return $
--       parensIf (k > 0) $
--         D.align $
--           D.group $
--             D.text "let" <+> parens (dx <> D.text "," <+> dy) <+> D.text "=" <+> D.align da
--               </> D.text "in" <+> D.align db

--   fununit a e = Printer $ \vn k -> do
--     da <- runPrinterI a 10
--     de <- runPrinterI e 0
--     return $
--       parensIf (k > 0) $
--         D.align $
--           D.group $
--             D.text "let () =" <+> D.align da
--               </> D.text "in" <+> D.align de

--   ftext s = Printer $ \_ k ->
--     return $ parensIf (k > 9) $ D.text "text" <+> D.text (show s)

--   fcat a b = Printer $ \vn k -> do
--     da <- runPrinterI a 5
--     db <- runPrinterI b 5
--     return $ parensIf (k > 5) $ D.group $ da </> D.text "<#>" <+> db

--   fbchoice a b = Printer $ \vn k -> do
--     da <- runPrinterI a 4
--     db <- runPrinterI b 4
--     return $ parensIf (k > 4) $ D.group $ da </> D.text "<?" <+> db

--   fempty = toPrinter $ D.text "empty"
--   fline = toPrinter $ D.text "line"
--   flinebreak = toPrinter $ D.text "linebreak"

--   fspace = toPrinter $ D.text "space"
--   fspaces = toPrinter $ D.text "spaces"

--   fline' = toPrinter $ D.text "line'"
--   fnespaces' = toPrinter $ D.text "nespaces'"

--   fgroup a = Printer $ \vn k -> do
--     da <- runPrinterI a 10
--     return $ parensIf (k > 9) $ D.text "group" <+> da

--   falign a = Printer $ \vn k -> do
--     da <- runPrinterI a 10
--     return $ parensIf (k > 9) $ D.text "align" <+> da

--   fnest n a = Printer $ \vn k -> do
--     da <- runPrinterI a 10
--     return $ parensIf (k > 9) $ D.text "nest" <+> ppr n <+> da

-- -- | An instance for pretty-printing recursive defined FliPpr expressions.
-- instance FliPprD (PrinterM s) (Printer s) (Printer s) where
--   fshare e = do
--     let md = runPrinterI e
--     (tbRef : _) <- ask
--     r <- newRef $ ()
--     modifyRef tbRef (M.insert r md)
--     return $ Pointer $ r

--   flocal m = Printer $ \vn k -> do
--     tbRef <- newRef $ M.empty
--     d <- RM.local (tbRef :) $ m >>= \e -> runPrinterI e 0
--     list <- M.toList <$> readRef tbRef
--     defs <-
--       D.group . D.align . (D.text "rec" <+>)
--         . D.foldDoc (\x y -> x </> D.text "and" <+> y)
--         <$> mapM
--           ( \(ref, mdef) -> do
--               def <- mdef
--               return $ D.group $ D.align (pprRef ref <+> D.nest 2 (D.text "=" </> def))
--           )
--           list
--     return $
--       parensIf (k > 0) $
--         D.align $
--           D.text "let" <+> D.align defs
--             </> D.text "in" <+> d

-- instance D.Pretty (FliPpr t) where
--   pprPrec k (FliPpr m) = runRefM (pprFliPpr m k)
--     where
--       pprFliPpr :: PrinterM s (Printer s (t :: FType)) -> Prec -> RefM s Doc
--       pprFliPpr m k =
--         runReaderT (runPrinterM $ runPrinterI (fal m) 0 k) []

-- instance Show (FliPpr t) where
--   show = show . ppr
