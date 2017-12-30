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

import Text.FliPpr.Doc as D
import Text.FliPpr.Internal.CPS 

data FType = D | Type :~> FType 


type In a = (Typeable a, Eq a)

data a <-> b = PInv String (a -> Maybe b) (b -> Maybe a) 

data Branch arg exp a (t :: FType) =
  forall b. In b => Branch (a <-> b) (arg b -> exp t)


class FliPprCPre (arg :: * -> *) (exp :: FType -> *) | exp -> arg where
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

class FliPprCPre arg exp => FliPprC arg exp | exp -> arg where
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
  ffix :: Container2 f => f (Rec f exp) -> CPS exp (f exp)
  flet :: exp t -> CPS exp (exp t) 
  flet = return 

newtype A arg a = A { unA :: arg a }
newtype E exp t = E { unE :: exp t }
type C exp = CPS exp 

newtype FliPpr t = FliPpr (forall arg exp. FliPprC arg exp => exp t)

flipprPure :: (forall arg exp. FliPprC arg exp => E exp t) -> FliPpr t
flipprPure x = FliPpr (unE x)

flippr :: (forall arg exp. FliPprC arg exp => C exp (E exp t)) -> FliPpr t
flippr x = flipprPure (unC x)

spaces :: FliPprC arg exp => E exp D
spaces = E fspaces 

space :: FliPprC arg exp => E exp D
space = E fspace

arg :: (In a, FliPprC arg exp) => (A arg a -> E exp t) -> E exp (a :~> t)
arg f = E (farg (coerce f))

app :: (In a, FliPprC arg exp) => E exp (a :~> t) -> A arg a -> E exp t 
app (E f) (A a) = E (fapp f a) 

(@@) :: (In a, FliPprC arg exp) => E exp (a :~> t) -> A arg a -> E exp t 
(@@) = app

infixr 0 @@

case_ :: (In a, FliPprC arg exp) => A arg a -> [Branch (A arg) (E exp) a r] -> E exp r
case_ (A a) bs = E (fcase a (coerce bs))

-- unpair :: (In a, In b, FliPprC arg exp) => A arg (a,b) -> (A arg a -> A arg b -> E exp r) -> E exp r
-- unpair (A x) k = E $ funpair x (coerce k)

unpair :: (In a, In b, FliPprC arg exp) => A arg (a,b) -> C exp (A arg a, A arg b)
unpair (A x) = CPS $ \k -> funpair x (coerce (curry k))

unC :: C exp (E exp a) -> E exp a
unC (CPS m) = E (m unE)

-- unpairC :: (In a, In b) => A arg (a,b) -> C arg exp r (A arg a, A arg b)
-- unpairC x = cont $ \k -> EUnPair x (curry k)

(<?) :: FliPprC arg exp => E exp D -> E exp D -> E exp D
(<?) (E x) (E y) = E (fbchoice x y)

infixr 4 <?

-- type C arg exp r a = Cont (E arg exp r) a 

-- unC :: C arg exp r (E arg exp r) -> E arg exp r
-- unC x = runCont x id 

-- call :: exp t -> E arg exp t
-- call = EVar 

-- mrec :: TypeList ts => (Apps exp ts -> Apps (E arg exp) ts) -> C arg exp r (Apps (E arg exp) ts)
-- mrec f = cont $ \k -> EMRec f (k . mapApps EVar)

share :: FliPprC arg exp => E exp t -> C exp (E exp t)
share e = E <$> flet (unE e)
  
fix1 :: FliPprC arg exp => (E exp t -> E exp t) -> E exp t
fix1 f = E $ runCPS (ffix (Single (Rec $ \(Single f_) -> unE (f (E f_)))))
                    (\(Single x) -> x)

fix2 :: FliPprC arg exp =>
        ((E exp a, E exp b) -> (E exp a, E exp b)) -> C exp (E exp a, E exp b)
fix2 f = toPair <$> ffix
         ((Rec $ \(f_ :< g_ :< End) -> unE $ fst $ f (E f_, E g_))
          :<
          (Rec $ \(f_ :< g_ :< End) -> unE $ snd $ f (E f_, E g_))
          :<
          End)
  where
    toPair (a :< b :< End) = (E a,E b) 

fixn :: (FliPprC arg exp, Container2 t) =>
        t (Rec t (E exp)) -> C exp (t (E exp))
fixn defs =
  fmap2 E <$> ffix (fmap2 (adjustRec2 unE E) defs)
                

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

  
hardcat :: FliPprC arg exp => E exp D -> E exp D -> E exp D
hardcat (E x) (E y) = E (fcat x y)

instance (D ~ t, FliPprC arg exp) => Semigroup (E exp t) where
  (<>) x y  = x `hardcat` (spaces `hardcat` y)

instance (D ~ t, FliPprC arg exp) => Monoid (E exp t) where
  mempty  = spaces -- ^ Notice, empty is not equal to memtpy.
  mappend = (<>) 

instance (D ~ t, FliPprC arg exp) => D.DocLike (E exp t) where
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

instance FliPprCPre (Printing D.Doc) (Printing D.Doc) where
  fapp (Printing f) x = Printing $ \fn vn k -> 
    let d1 = f fn vn 9
        d2 = unPrinting x fn vn 10 
    in D.parensIf (k > 9) $ D.group $ d1 D.<+> D.text "`app`" D.<+> d2

  farg f = Printing $ \fn vn k -> 
    let vn' = vn + 1 
        d = unPrinting (f (varArg vn')) fn vn' 1
    in parensIf (k > 1) $ D.group $ 
       D.text "arg" D.<+> D.text "$" D.<+> (D.text "\\" D.<> (pprVName vn' D.<+> D.nest 2 (D.text "->" D.</> d)))

  fcase x bs = Printing $ \fn vn k ->
    let ds = map (pprBranch fn vn) bs
    in  parensIf (k > 9) $
      D.text "case_" D.<+>
      unPrinting x fn vn 10 D.</>
      D.nest 2 (D.group (D.text "[" D.<> D.align (D.punctuate (D.text "," D.<> D.line) ds D.<> D.text "]")))
      where
        pprBranch fn vn (Branch (PInv s _ _) f) = 
          let d = unPrinting (f (varArg (vn+1))) fn (vn+1) 0
          in D.text s D.<+>
             D.text "`Branch`" D.<+> D.align (D.text "\\" D.<> pprVName (vn+1) D.<+> D.text "->" D.<+> d)

  funpair x f = Printing $ \fn vn k -> 
    let d = unPrinting (f (varArg (vn+1)) (varArg (vn+2))) fn (vn+2) 1
    in parensIf (k > 1) $
       D.text "unpair" D.<+> unPrinting x fn vn 10 D.<+> 
       D.text "$" D.<+> D.text "\\" D.<> pprVName (vn+1) D.<+> pprVName (vn+2) D.<+> D.text "->" D.<>
       D.nest 2 (D.line D.<> d)
     
  ftext s = Printing $ \_fn _vn k -> 
    parensIf (k > 9) $
    D.text "text" D.<+> D.ppr s

  fcat x y = Printing $ \fn vn k ->
    let d1 = unPrinting x fn vn 9
        d2 = unPrinting y fn vn 9
    in parensIf (k > 9) $
       d1 D.<+> D.text "`hardcat`" D.<+> d2

  fbchoice x y = Printing $ \fn vn k -> 
    let d1 = unPrinting x fn vn 4 
        d2 = unPrinting y fn vn 4 
    in parensIf (k > 4) $
       D.align d1 D.<> D.line D.<> D.text "<?" D.<+> d2 

  fempty = fromDoc (D.text "empty")
  fline  = fromDoc (D.text "line")
  flinebreak = fromDoc (D.text "linebreak")

  fspace  = fromDoc (D.text "space")
  fspaces = fromDoc (D.text "spaces")


  falign e = Printing $ \fn vn k -> 
    let d = unPrinting e fn vn 10
    in parensIf (k > 9) $ D.text "align" D.<+> D.align d 

  fgroup e = Printing $ \fn vn k -> 
    let d = unPrinting e fn vn 10
    in parensIf (k > 9) $ D.align (D.text "group" D.<> D.nest 2 (D.line D.<> D.align d ))

  fnest i e = Printing $ \fn vn k -> 
    let d = unPrinting e fn vn 10
    in parensIf (k > 9) $ D.text "nest" D.<+> D.ppr i D.<+> D.align d 


instance FliPprC (Printing D.Doc) (Printing D.Doc) where
  ffix :: forall f. Container2 f =>
          f (Rec f (Printing D.Doc)) -> C (Printing D.Doc) (f (Printing D.Doc))
  ffix defs = CPS $ \cont -> Printing $ \fn vn k ->
    let fn' = length2 defs + fn
        fs  = evalState
                (traverse2 (const $ state $ \i -> (Printing $ \_ _ _ -> pprFName i, i+1)) defs)
                fn
        ns  = fold2 (\p -> [unPrinting p fn' vn 0])             fs
        ds  = fold2 (\a -> [unPrinting (pprDef fs a) fn' vn 0]) defs
    in parensIf (k > 0) $ D.align $ 
       D.align (D.text "letrec" D.<+>
                trav (zipWith (\a b -> a D.<+> D.text "=" D.<+> D.align b) ns ds)
               )
       D.</>
       D.text "in" D.<+> D.align (unPrinting (cont fs) fn' vn 0)
    where
      pprDef fs (Rec f) = f fs

      trav []  = D.empty
      trav [d] = d
      trav (d:ds) = d D.</> D.text "   and" D.<+> trav ds

  flet :: Printing D.Doc a -> C (Printing D.Doc) (Printing D.Doc a)
  flet a = CPS $ \cont -> Printing $ \fn vn k ->
    let fn' = fn + 1
        v   = Printing $ \_ _ _ -> pprFName fn
    in parensIf (k > 0) $ D.align $ 
         D.align (D.text "let" D.<+>
                    pprFName fn D.<+> D.text "=" D.<+>
                     D.align (unPrinting a fn' vn 0))         
         D.</>
         D.text "in" D.<+> D.align (unPrinting (cont v) fn' vn 0)
      
  


instance (exp ~ Printing D.Doc) => D.Pretty (E exp t) where
  pprPrec k e = unPrinting (unE e) 0 0 k 


instance D.Pretty (FliPpr t) where
  pprPrec k (FliPpr e) = unPrinting e 0 0 k

instance Show (FliPpr t) where
  show = show . ppr 


example1 :: FliPpr ([Bool] :~> D)
example1 = flippr $ do
  let manyParens d = fix1 (\m -> d <? parens m)

  pprTF <- share $ arg $ \i -> manyParens $ case_ i
        [ unTrue  `Branch` \_ -> text "True",
          unFalse `Branch` \_ -> text "False" ]

  (ppr, _ppr') <- fix2 $ \(~(_ppr, ppr')) ->
    let ppr_ = arg $ \x -> case_ x
              [ unNil `Branch` \_ -> text "[" <> text "]",
                unCons `Branch` \xx -> unC $ do
                  (a,x) <- unpair xx
                  return $ brackets (ppr' `app` a `app` x)]
        ppr'_ = arg $ \a -> arg $ \x -> case_ x
          [ unNil `Branch` \_ -> pprTF `app` a
              , unCons `Branch` \xx -> unC $ do
                  (b,x) <- unpair xx
                  return $ pprTF `app` a <> text "," <> ppr' `app` b `app` x]
    in (ppr_, ppr'_)
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
  
    
