{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module Text.FliPpr.Internal.Type
  ( FType (..),
    type D,
    type (~>),
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
    charAs,
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
    Repr (..),
    FliPprM,
    mfixF,
    letr, letrs,
    def,
    share,
    local,
    FinNE,
    reifySNat,
    -- Wit (..),

    type Lift, type (**), Defs.LetArg, -- Defs.Convertible,
    Defs.DefType, Defs, DefsF,
  )
where

import           Control.Applicative       (Const (..))
import           Control.Monad.Reader      hiding (lift, local)
import           Control.Monad.State       hiding (lift)
import           Data.Coerce               (coerce)
import qualified Data.Fin                  as F
import           Data.Kind                 (Type)
import           Data.Semigroup            (Semigroup (..))
import qualified Data.Type.Nat             as F
import           Data.Typeable             (Proxy (..))
import           Text.FliPpr.Doc           as D
import           Text.FliPpr.Internal.Defs (Defs, type (**), type Lift)
import qualified Text.FliPpr.Internal.Defs as Defs

import           Control.Arrow             (first)

import qualified Data.RangeSet.List        as RS

-- | A kind for datatypes in FliPpr.
data FType = FTypeD | Type :~> FType

-- | Unticked synonym for :~>
type a ~> b = a ':~> b

-- | Unticked synonym for FTypeD
type D = 'FTypeD

type In a = Eq a

-- | A type for partial bijections. The 'String'-typed field will be used in pretty-printing
--   of FliPpr expressions.
data PartialBij a b = PartialBij !String !(a -> Maybe b) !(b -> Maybe a)

-- | A datatype represents branches.
data Branch arg exp a (t :: FType)
  = forall b. In b => Branch (PartialBij a b) (arg b -> exp t)

-- | A finally-tagless implementation of FliPpr expressions.
--   The APIs are only for internal use.
class FliPprE (arg :: Type -> Type) (exp :: FType -> Type) | exp -> arg where
  fapp :: In a => exp (a ~> t) -> arg a -> exp t
  farg :: In a => (arg a -> exp t) -> exp (a ~> t)

  fcase :: In a => arg a -> [Branch arg exp a t] -> exp t

  funpair :: (In a, In b) => arg (a, b) -> (arg a -> arg b -> exp t) -> exp t
  fununit :: arg () -> exp t -> exp t

  fbchoice :: exp D -> exp D -> exp D

  -- Output character as is, if it is contained in the given set
  fcharAs :: arg Char -> RS.RSet Char -> exp D

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

-- | @A arg a@ is nothing but @arg a@, but used for controlling type inference.
newtype A (arg :: Type -> Type) (a :: Type) = A {unA :: arg a}

-- | Similarly, @E exp t@ is nothing but @exp t@.
newtype E (exp :: FType -> Type) (t :: FType) = E {unE :: exp t}

newtype FliPpr t = FliPpr (forall arg exp. FliPprD arg exp => exp t)

-- flipprPure :: (forall arg exp. FliPprD arg exp => E exp t) -> FliPpr t
-- flipprPure x = FliPpr (unE x)

type FliPprM exp = Defs.DefM (E exp)

-- | Make a closed FliPpr definition. A typical use is:
--
--   > flippr $ do
--   >   rec ppr <- share $ arg $ \i -> ...
--   >   return ppr
flippr :: (forall arg exp. FliPprD arg exp => FliPprM exp (E exp t)) -> FliPpr t
flippr x = FliPpr (unE $ Defs.local x) -- flipprPure (unC x)

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
arg :: (In a, FliPprE arg exp) => (A arg a -> E exp t) -> E exp (a ~> t)
arg f = E (farg (coerce f))

-- | A wrapper for 'fapp'.
{-# INLINEABLE app #-}
app :: (In a, FliPprE arg exp) => E exp (a ~> t) -> A arg a -> E exp t
app (E f) (A a) = E (fapp f a)

-- | FliPpr version of '$'.
{-# INLINE (@@) #-}
(@@) :: (In a, FliPprE arg exp) => E exp (a ~> t) -> A arg a -> E exp t
(@@) = app

infixr 0 @@

charAs :: FliPprE arg exp => A arg Char -> RS.RSet Char -> E exp D
charAs a cs = E $ fcharAs (unA a) cs

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

instance Defs.Defs e => Defs.Defs (E e) where
  newtype Fs (E e) a = RE (Defs.Fs e a)

  liftDS (E x) = RE (Defs.liftDS x)
  unliftDS (RE x) = E (Defs.unliftDS x)

  pairDS (RE r1) (RE r2) = RE (Defs.pairDS r1 r2)

  --  unpairRules (RE e) k = RE $ unpairRules e (coerce k)

  letrDS h = RE $ Defs.letrDS (coerce h)

infixr 4 <?

-- |
-- The type class 'Repr' provides the two method 'toFunction' and 'fromFunction'.
class Repr (arg :: Type -> Type) exp (t :: FType) r | exp -> arg, r -> arg exp t where
  toFunction :: E exp t -> r
  -- ^ @toFunction :: E exp (a1 ~> ... ~> an ~> D) -> A arg a1 -> ... -> A arg an -> E exp D@

  fromFunction :: r -> E exp t
  -- ^ @fromFunction :: A arg a1 -> ... -> A arg an -> E exp D -> E exp (a1 ~> ... ~> an ~> D)@

instance FliPprE arg exp => Repr arg exp t (E exp t) where
  toFunction = id
  fromFunction = id

instance (FliPprE arg exp, Repr arg exp t r, In a) => Repr arg exp (a ~> t) (A arg a -> r) where
  toFunction f = \a -> toFunction (f `app` a)
  fromFunction k = arg (fromFunction . k)

-- | A specialized version of 'mfixDefM'
-- mfixF :: forall exp a d. (Defs exp, Defs.DefType d, Defs.Convertible (E exp) d a) => (a -> FliPprM exp a) -> FliPprM exp a
mfixF :: Defs.LetArg (E f) a => (a -> FliPprM f a) -> FliPprM f a
mfixF = Defs.mfixDefM

type DefsF exp = Defs.DTypeVal (E exp)

-- | A specialized version of 'letr', which would be useful for defining mutual recursions.
--
--- Typical usage:
--  @
--  letr $ \f -> def fdef $
--  letr $ \g -> def gdef $
--    code_using_f_and_g
--  @
--
--  @
--  letr $ \f -> letr $ \g ->
--    -- f and g can be mutualy dependent
--    def fdeF >>>
--    def gdef $
--    code_using_f_and_g
--  @
--
letr :: (Repr arg exp ft rep, FliPprD arg exp) => (rep -> FliPprM exp (rep, r)) -> FliPprM exp r
letr h = Defs.letr $ \x -> do
  (d, r) <- h (toFunction x)
  return (fromFunction d, r)

-- not efficient for large list
letrs :: (Repr arg exp ft rep, FliPprD arg exp, Eq k) => [k] -> ((k -> rep) -> FliPprM exp (k -> rep, r)) -> FliPprM exp r
letrs [] f = snd <$> f (const $ error "letrs: out of bounds")
letrs (k:ks) f = letr $ \f1 -> letrs ks $ \frest -> do
  (rf, rest) <- f $ \k' -> if k' == k then f1 else frest k'
  return (rf, (rf k, rest))

-- letrs = go []
--   where
--     unJust (Just x) = x
--     unJust Nothing  = "letrs: out of bounds"


-- | Useful combinator that can be used with 'letr'.
def :: Monad m => a -> m b -> m (a, b)
def a b = (a,) <$> b

-- | Spacilized version of 'Defs.share'
share ::(Repr arg exp ft rep,  FliPprD arg exp) => rep -> FliPprM exp rep
share = fmap toFunction . Defs.share . fromFunction

-- | Specialized version of 'Defs.local'
local :: (Repr arg exp ft rep, FliPprD arg exp) => FliPprM exp rep -> rep
local = toFunction . Defs.local . fmap fromFunction

-- One-level unfolding to avoid overlapping instances.

instance Defs.Defs exp => Defs.LetArg (E exp) (E exp a) where
  letrGen f = Defs.letr f

instance (FliPprE arg exp, In a, Repr arg exp t r, Defs.Defs exp) => Defs.LetArg (E exp) (A arg a -> r) where
  letrGen f = Defs.letr $ fmap (first fromFunction) . f . toFunction


-- instance Defs.Convertible (E exp) (Defs.Lift a) (E exp a) where
--   fromDTypeVal (Defs.VT x) = x
--   toDTypeVal x = return $ Defs.VT x

-- instance (FliPprE arg exp, In a, Repr arg exp t r) => Defs.Convertible (E exp) (Defs.Lift (a ~> t)) (A arg a -> r) where
--   toDTypeVal = return . Defs.VT . fromFunction
--   fromDTypeVal (Defs.VT x) = toFunction x

-- instance Convertible (E exp) t r => Convertible (E exp) t (FinNE F.Z -> r) where
--   toDTypeVal x = toDTypeVal (x F.FZ)
--   fromDTypeVal n = const (fromDTypeVal n)

-- instance (Convertible (E exp) t r, Convertible (E exp) ts (FinNE n -> r)) => Convertible (E exp) (t :*: ts) (FinNE (F.S n) -> r) where
--   toDTypeVal x = VProd <$> toDTypeVal (x F.FZ) <*> toDTypeVal (\n -> x (F.FS n))
--   fromDTypeVal (VProd v0 h) = \x -> case x of
--     F.FZ -> fromDTypeVal v0
--     F.FS n -> fromDTypeVal h n

-- type family Prods t (n :: F.Nat) = r where
--   Prods t 'F.Z = t
--   Prods t ( 'F.S n) = t ** Prods t n

-- newtype ToDTypeVal exp r t m = ToDTypeVal {runToDTypeVal :: (FinNE m -> r) -> Defs.DefM (E exp) (Defs.DTypeVal (E exp) (Prods t m))}

-- newtype FromDTypeVal exp r t m = FromDTypeVal {runFromDTypeVal :: Defs.DTypeVal (E exp) (Prods t m) -> FinNE m -> r}

-- instance (Defs.Convertible (E exp) t r, F.SNatI m, ts ~ Prods t m) => Defs.Convertible (E exp) ts (FinNE m -> r) where
--   toDTypeVal :: (FinNE m -> r) -> Defs.DefM (E exp) (Defs.DTypeVal (E exp) (Prods t m))
--   toDTypeVal = runToDTypeVal $ F.induction f0 fstep
--     where
--       f0 = ToDTypeVal $ \f -> Defs.toDTypeVal (f F.FZ)

--       fstep :: forall k. F.SNatI k => ToDTypeVal exp r t k -> ToDTypeVal exp r t ( 'F.S k)
--       fstep p = ToDTypeVal $ \f -> Defs.VProd <$> Defs.toDTypeVal (f F.FZ) <*> runToDTypeVal p (f . F.FS)

--   fromDTypeVal :: Defs.DTypeVal (E exp) (Prods t m) -> FinNE m -> r
--   fromDTypeVal = runFromDTypeVal $ F.induction f0 fstep
--     where
--       f0 = FromDTypeVal $ \x _ -> Defs.fromDTypeVal x
--       fstep :: forall k. F.SNatI k => FromDTypeVal exp r t k -> FromDTypeVal exp r t ( 'F.S k)
--       fstep p = FromDTypeVal $ \(Defs.VProd v0 h) x -> case x of
--         F.FZ   -> Defs.fromDTypeVal v0
--         F.FS n -> runFromDTypeVal p h n

-- | FinNE n represents {0,..,n} (NB: n is included)
type FinNE n = F.Fin ( 'F.S n)

-- data Wit c where
--   Wit :: c => Wit c

-- newtype Wit' t n = Wit' (Wit (Defs.DefType (Prods t n)))

-- propDefTypeProds :: forall n t. (Defs.DefType t, F.SNatI n) => Proxy n -> Proxy t -> Wit (Defs.DefType (Prods t n))
-- propDefTypeProds _ _ = case F.induction @n f0 fstep of Wit' w -> w
--   where
--     f0 :: Wit' t 'F.Z
--     f0 = Wit' Wit
--     fstep :: forall k. Wit' t k -> Wit' t ( 'F.S k)
--     fstep (Wit' Wit) = Wit' Wit

-- reifySNat :: forall n r. (Integral n) => n -> (forall m. F.SNatI m => F.SNat m -> (forall t. Defs.DefType t => Proxy t -> Wit (Defs.DefType (Prods t m))) -> r) -> r
-- reifySNat n k = F.reify (fromIntegral n) $ \(_ :: Proxy k) -> k (F.snat @k) (\(_ :: Proxy t) -> propDefTypeProds @k Proxy (Proxy :: Proxy t))

reifySNat :: forall n r. Integral n => n -> (forall m. F.SNatI m => F.SNat m -> r) -> r
reifySNat n k = F.reify (fromIntegral n) $ \(_ :: Proxy m) -> k (F.snat :: F.SNat m)

-- where
--   makeWit :: forall n r. F.SNatI n => (forall a. DefType (Prods (T a) n) => Proxy a -> r) -> r
--   makeWit = case F.snat :: F.SNat n of
--     F.SZ -> k Proxy
--     F.SS -> makeWit k

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

-- newtype Defs.PprDefs (a :: FType) = Defs.PprDefs {Defs.pprDefs :: Prec -> State (RName, IName) D.Doc}

newtype VarMFliPpr a = VarMFliPpr {runVarMFliPpr :: State (RName, IName) a}
  deriving (Functor, Applicative, Monad, MonadState (RName, IName))

instance Defs.VarM VarMFliPpr where
  newVar = do
    rn <- newRName
    return $ "f" ++ show rn
  nestScope = id

newIName :: VarMFliPpr IName
newIName = do
  (i, v) <- get
  let !v' = v + 1
  put (i, v')
  return v

newRName :: VarMFliPpr RName
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

type PrinterI = Defs.PprDefs VarMFliPpr :: FType -> Type

instance FliPprE (Const IName) PrinterI where
  fapp e1 e2 = Defs.PprDefs $ \k -> do
    d1 <- Defs.pprDefs e1 9
    let d2 = pprIName (getConst e2)
    return $ D.parensIf (k > 9) $ d1 D.<+> d2

  farg h = Defs.PprDefs $ \k -> do
    x <- newIName
    d <- Defs.pprDefs (h $ Const x) 0
    return $ D.parensIf (k > 0) $ D.text "\\" <> pprIName x <+> D.text "->" </> d

  fcharAs a cs = Defs.PprDefs $ \k -> do
    let da = pprIName $ getConst a
    return $ parensIf (k > 9) $ da D.<+> D.text "`charAs`" D.<+> D.text (show cs)

  fcase a bs = Defs.PprDefs $ \k -> do
    let da = pprIName $ getConst a
    ds <- forM bs $ \(Branch (PartialBij s _ _) f) -> do
      x <- newIName
      df <- Defs.pprDefs (f $ Const x) 0
      return $ D.group $ D.nest 2 $ D.text s <+> D.text "$" <+> D.text "\\" <> pprIName x <+> D.text "->" <+> df
    return $
      parensIf (k > 9) $
        D.group $
          D.text "case_" <+> da
            <+> D.text "[" <> D.align (foldDoc (\x y -> x <> D.text "," </> y) ds <> D.text "]")

  funpair a f = Defs.PprDefs $ \k -> do
    let da = pprIName (getConst a)
    x <- newIName
    y <- newIName
    db <- Defs.pprDefs (f (Const x) (Const y)) 0
    return $
      parensIf (k > 0) $
        D.align $
          D.group $
            D.text "let" <+> parens (pprIName x <> D.text "," <+> pprIName y) <+> D.text "=" <+> D.align da
              </> D.text "in" <+> D.align db

  fununit a e = Defs.PprDefs $ \k -> do
    let da = pprIName (getConst a)
    de <- Defs.pprDefs e 0
    return $
      D.parensIf (k > 0) $
        D.align $
          D.group $
            D.text "let () =" <+> D.align da
              </> D.text "in" <+> D.align de

  ftext s = Defs.PprDefs $ \k ->
    return $ parensIf (k > 9) $ D.text "text" <+> D.text (show s)

  fcat a b = Defs.PprDefs $ \k -> do
    da <- Defs.pprDefs a 5
    db <- Defs.pprDefs b 5
    return $ parensIf (k > 5) $ D.group $ da </> D.text "<#>" <+> db

  fbchoice a b = Defs.PprDefs $ \k -> do
    da <- Defs.pprDefs a 4
    db <- Defs.pprDefs b 4
    return $ parensIf (k > 4) $ D.group $ da </> D.text "<?" <+> db

  fempty = Defs.PprDefs $ const $ return $ D.text "empty"
  fline = Defs.PprDefs $ const $ return $ D.text "line"
  flinebreak = Defs.PprDefs $ const $ return $ D.text "linebreak"

  fspace = Defs.PprDefs $ const $ return $ D.text "space"
  fspaces = Defs.PprDefs $ const $ return $ D.text "spaces"

  fline' = Defs.PprDefs $ const $ return $ D.text "line'"
  fnespaces' = Defs.PprDefs $ const $ return $ D.text "nespaces'"

  fgroup a = Defs.PprDefs $ \k -> do
    da <- Defs.pprDefs a 10
    return $ parensIf (k > 9) $ D.text "group" <+> da

  falign a = Defs.PprDefs $ \k -> do
    da <- Defs.pprDefs a 10
    return $ parensIf (k > 9) $ D.text "align" <+> da

  fnest n a = Defs.PprDefs $ \k -> do
    da <- Defs.pprDefs a 10
    return $ parensIf (k > 9) $ D.text "nest" <+> ppr n <+> da

instance D.Pretty (FliPpr t) where
  pprPrec _ (FliPpr m) = evalState (runVarMFliPpr $ Defs.pprDefs m 0) (0, 0)

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

-- Defs.pprDefs ::inter s a -> VCount -> Prec -> PrinterM s Doc
-- Defs.pprDefs (Pter f) vn k = f vn k
-- Defs.pprDefs (Pter p) _ _ = return $ pprRef p

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
--     df <- Defs.pprDefs (foPrinter $ pprVName vn)) (vn + 1) 0
--     return $ D.group $ D.nest 2 $ parensIf (k > 0) $ D.text "\\" <> pprVName vn <+> D.text "->" </> df

--   fapp f a = Printer $ \vn k -> do
--     df <- Defs.pprDefs f 9
--     da <- Defs.pprDefs a 10
--     return $ parensIf (k > 9) $ df <+> da

--   fcase a bs = Printer $ \vn k -> do
--     da <- Defs.pprDefs a 10
--     ds <-
--       mapM
--         ( \(Branch (PartialBij s _ _) f) -> do
--             df <- Defs.pprDefs (foPrinter $ pprVName vn)) (vn + 1) 0
--             return $ D.group $ D.nest 2 $ D.text s <+> D.text "$" <+> D.text "\\" <> pprVName vn <+> D.text "->" <+> df
--         )
--         bs
--     return $
--       parensIf (k > 9) $
--         D.group $
--           D.text "case_" <+> da
--             <+> D.text "[" <> D.align (foldDoc (\x y -> x <> D.text "," </> y) ds <> D.text "]")

--   funpair a f = Printer $ \vn k -> do
--     da <- Defs.pprDefs a 10
--     let dx = pprVName vn
--     let dy = pprVName (vn + 1)
--     db <- Defs.pprDefs (foPrinter dx) (toPrinter dy)) (vn + 2) 0
--     return $
--       parensIf (k > 0) $
--         D.align $
--           D.group $
--             D.text "let" <+> parens (dx <> D.text "," <+> dy) <+> D.text "=" <+> D.align da
--               </> D.text "in" <+> D.align db

--   fununit a e = Printer $ \vn k -> do
--     da <- Defs.pprDefs a 10
--     de <- Defs.pprDefs e 0
--     return $
--       parensIf (k > 0) $
--         D.align $
--           D.group $
--             D.text "let () =" <+> D.align da
--               </> D.text "in" <+> D.align de

--   ftext s = Printer $ \_ k ->
--     return $ parensIf (k > 9) $ D.text "text" <+> D.text (show s)

--   fcat a b = Printer $ \vn k -> do
--     da <- Defs.pprDefs a 5
--     db <- Defs.pprDefs b 5
--     return $ parensIf (k > 5) $ D.group $ da </> D.text "<#>" <+> db

--   fbchoice a b = Printer $ \vn k -> do
--     da <- Defs.pprDefs a 4
--     db <- Defs.pprDefs b 4
--     return $ parensIf (k > 4) $ D.group $ da </> D.text "<?" <+> db

--   fempty = toPrinter $ D.text "empty"
--   fline = toPrinter $ D.text "line"
--   flinebreak = toPrinter $ D.text "linebreak"

--   fspace = toPrinter $ D.text "space"
--   fspaces = toPrinter $ D.text "spaces"

--   fline' = toPrinter $ D.text "line'"
--   fnespaces' = toPrinter $ D.text "nespaces'"

--   fgroup a = Printer $ \vn k -> do
--     da <- Defs.pprDefs a 10
--     return $ parensIf (k > 9) $ D.text "group" <+> da

--   falign a = Printer $ \vn k -> do
--     da <- Defs.pprDefs a 10
--     return $ parensIf (k > 9) $ D.text "align" <+> da

--   fnest n a = Printer $ \vn k -> do
--     da <- Defs.pprDefs a 10
--     return $ parensIf (k > 9) $ D.text "nest" <+> ppr n <+> da

-- -- | An instance for pretty-printing recursive defined FliPpr expressions.
-- instance FliPprD (PrinterM s) (Printer s) (Printer s) where
--   fshare e = do
--     let md = Defs.pprDefs e
--     (tbRef : _) <- ask
--     r <- newRef $ ()
--     modifyRef tbRef (M.insert r md)
--     return $ Pointer $ r

--   flocal m = Printer $ \vn k -> do
--     tbRef <- newRef $ M.empty
--     d <- RM.local (tbRef :) $ m >>= \e -> Defs.pprDefs e 0
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
--         runReaderT (runPrinterM $ Defs.pprDefs (fal m) 0 k) []

-- instance Show (FliPpr t) where
--   show = show . ppr
