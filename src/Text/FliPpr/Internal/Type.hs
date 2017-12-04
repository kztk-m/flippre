{-# LANGUAGE TypeFamilyDependencies #-}
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

{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fwarn-unused-imports -fwarn-incomplete-patterns #-}

{-# LANGUAGE NoMonomorphismRestriction #-}

module Text.FliPpr.Internal.Type where

import Data.Kind 
import Control.Monad.Cont 
import Control.Applicative (Const(..))

import Data.Typeable
import Data.Monoid (Endo(..))
import Data.Functor.Identity (Identity(..))
import Text.FliPpr.Doc as D 

import Debug.Trace

data FType = D | Type :~> FType 


type In a = (Typeable a, Eq a)

data a <-> b = PInv String (a -> Maybe b) (b -> Maybe a) 

data Branch arg exp a (t :: FType) =
  forall b. In b => Branch (a <-> b) (arg b -> exp t)

newtype ((f :: k' -> Type) :.: (g :: k -> k')) a = Comp { getComp :: (f (g a)) }

infixl 5 :.:

data Apps (f :: k -> Type) (t :: [k]) where
  End  :: Apps f '[]
  (:>) :: f a -> Apps f r -> Apps f (a : r)

data TLWit (t :: [k]) where
  WNil  :: TLWit '[]
  WCons :: Proxy a -> TLWit r -> TLWit (a : r)
  
-- type family Map (f :: k -> k) (t :: [k]) = (r :: [k]) | r -> t where
--   Map f '[]     = '[]
--   Map f (a : t) = f a : Map f t 

-- type family MapF (f :: FType -> k) (t :: [FType]) = (r :: [k]) | r -> t where
--   MapF f '[]     = '[]
--   MapF f (a : t) = f a : Map f t 


tlLength :: TLWit t -> Int
tlLength WNil = 0
tlLength (WCons _ r) = 1 + tlLength r

genFromTL :: TLWit t -> b -> (forall t. b -> (f t, b)) -> Apps f t
genFromTL WNil        b gen = End 
genFromTL (WCons _ r) b gen =
  let (a, b') = gen b
  in a :> genFromTL r b' gen  

fromTL :: TLWit t -> Apps (Const ()) t
fromTL WNil = End
fromTL (WCons _ r) = Const () :> fromTL r 

traverseApps :: Applicative m => (forall a. f a -> m (g a)) -> Apps f t -> m (Apps g t)
traverseApps f End = pure End
traverseApps f (a :> r) = (:>) <$> f a <*> traverseApps f r 


appsLength :: forall t. TypeList t => Proxy t -> Int
appsLength _ = tlLength (wit :: TLWit t)

appsInit :: forall t f b. TypeList t =>
            Proxy t -> b -> (forall t. b -> (f t, b)) -> Apps f t
appsInit _ = genFromTL (wit :: TLWit t)

appsShape :: forall t. TypeList t =>
             Proxy t -> Apps (Const ()) t
appsShape _ = fromTL (wit :: TLWit t)              

zipWithApps :: (forall t. f t -> g t -> h t) -> Apps f t -> Apps g t -> Apps h t
zipWithApps f End End = End
zipWithApps f (a :> r) (b :> t) = f a b :> zipWithApps f r t

class TypeList (t :: [k]) where
--  data Apps (f :: k -> Type) t :: * 
  wit :: TLWit t 
  
  -- appsLength :: Proxy t -> Int
  -- appsInit   :: Proxy t -> b -> (forall t. b -> (f t, b)) -> Apps f t
  -- appsShape  :: Proxy t -> Apps (Const ()) t
  
  -- composeApps :: Apps f (Map g t) -> Apps (f :.: g) t 
  -- decomposeApps :: Apps (f :.: g) t -> Apps f (Map g t)

instance TypeList '[] where
--  data Apps f '[] = End 
  wit = WNil 
  
  -- appsLength _     = 0
  -- appsInit   _ _ f = End

  -- appsShape _      = End 


  -- composeApps End = End 
  -- decomposeApps End = End 
  
instance TypeList ts => TypeList (a ': ts) where
--  data Apps f (a ': ts) = f a :> Apps f ts 
  wit = WCons Proxy wit 
  
  -- appsLength _ = 1 + appsLength (Proxy :: Proxy ts)
  -- appsInit   _ s f = let (a,s') = f s
  --                    in a :> appsInit (Proxy) s' f 
  -- appsShape _ = Const () :> appsShape (Proxy :: Proxy ts)


  -- composeApps (a :> r) = Comp a :> composeApps r 
  -- decomposeApps (Comp a :> r) = a :> decomposeApps r 

  

foldApps :: (Monoid m) => (forall t. f t -> m) -> Apps f ts -> m
foldApps f = getConst . traverseApps (\a -> Const (f a))

foldrApps :: (forall t. f t -> b -> b) -> b -> Apps f ts -> b
foldrApps f = flip $ appEndo . foldApps (\a -> Endo (f a))

mapApps :: (forall t. f t -> g t) -> Apps f ts -> Apps g ts
mapApps f = runIdentity . traverseApps (Identity . f) 

infixr 5 :> 

class TypeList ts => FromList a exp ts where 
  appsFromList :: [ exp a ] -> Maybe (Apps exp ts)
  appsToList   :: Apps exp ts -> Maybe [ exp a ] 

instance FromList a exp '[] where
  appsFromList [] = Just End
  appsFromList _  = Nothing

  appsToList End = Just []


instance (Typeable a, Typeable b, FromList a exp r) => FromList a exp (b ': r) where
  appsFromList (a : x) = do
    r <- appsFromList x :: Maybe (Apps exp r)
    case eqT :: Maybe (a :~: b) of
      Just Refl -> return $ a :> r
      Nothing   -> Nothing 
  appsFromList _ = Nothing

  appsToList (a :> x) = do
    r <- appsToList x :: Maybe [exp a]
    case eqT :: Maybe (a :~: b) of
      Just Refl -> return $ a : r
      Nothing   -> Nothing

-- type family Append (xs :: [k]) (ys :: [k]) :: [k]
-- type instance Append '[] ys       = ys
-- type instance Append (x ': xs) ys = x ': Append xs ys 

class FliPprC (arg :: * -> *) (exp :: FType -> *) | exp -> arg where
  fapp   :: In a => exp (a :~> t) -> arg a -> exp t
  farg   :: In a => (arg a -> exp t) -> exp (a :~> t)

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

  ffix :: TypeList fs => (Apps exp fs -> Apps exp fs) -> (Apps exp fs -> exp t) -> exp t 

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

newtype A arg a = A { unA :: arg a }

data E arg exp (t :: FType) where
  EApp       :: In a => E arg exp (a :~> t) -> A arg a -> E arg exp t
  EArg       :: In a => (A arg a -> E arg exp t) -> E arg exp (a :~> t)
  ECase      :: In a => A arg a -> [Branch (A arg) (E arg exp) a t] -> E arg exp t
  EUnPair    :: (In a, In b) => A arg (a, b) -> (A arg a -> A arg b -> E arg exp t) -> E arg exp t

  EBChoice   :: E arg exp D -> E arg exp D -> E arg exp D
  
  EText      :: String -> E arg exp D
  EEmpty     :: E arg exp D
  ECat       :: E arg exp D -> E arg exp D -> E arg exp D
  
  ESpace     :: E arg exp D
  ESpaces    :: E arg exp D

  ELine      :: E arg exp D
  ELineBreak :: E arg exp D
  EAlign     :: E arg exp D -> E arg exp D
  EGroup     :: E arg exp D -> E arg exp D
  ENest      :: Int -> E arg exp D -> E arg exp D 

  EVar       :: exp t -> E arg exp t 
  EMRec      :: TypeList ts => (Apps exp ts -> Apps (E arg exp) ts) -> (Apps exp ts -> E arg exp r) -> E arg exp r


compile :: E arg exp t -> FliPprC arg exp => exp t 
compile (EApp e (A a))   = fapp (compile e) a
compile (EArg f)         = farg (compile . f . A)

compile (ECase (A x) bs) = fcase x (map conv bs)
  where
    conv (Branch bi f)    = Branch bi (compile . f . A)
compile (EUnPair (A p) f) = funpair p (\x y -> compile (f (A x) (A y)))

compile (EBChoice x y)    = fbchoice (compile x) (compile y)

compile (EText s) = ftext s
compile (EEmpty)  = fempty
compile (ECat e1 e2) = fcat (compile e1) (compile e2)
compile (ESpace) = fspace
compile (ESpaces) = fspaces
compile ELine = fline
compile ELineBreak = flinebreak
compile (EAlign e) = falign (compile e)
compile (EGroup e) = fgroup (compile e)
compile (ENest i e) = fnest i (compile e) 
compile (EVar e)    = e 
compile (EMRec f k)  =
  ffix (mapApps compile . f) (compile . k)

data FliPpr t = FliPpr (forall arg exp. FliPprC arg exp => exp t)

flippr :: (forall arg exp. E arg exp t) -> FliPpr t
flippr x = FliPpr (compile x) -- (compileR (fmap ERec x >>= id))

spaces :: E arg exp D
spaces = ESpaces

space :: E arg exp D
space = ESpace

arg :: In a => (A arg a -> E arg exp t) -> E arg exp (a :~> t)
arg = EArg

app :: In a => E arg exp (a :~> t) -> A arg a -> E arg exp t 
app = EApp

(@@) :: In a => E arg exp (a :~> t) -> A arg a -> E arg exp t 
(@@) = app

infixr 0 @@

case_ :: In a => A arg a -> [Branch (A arg) (E arg exp) a r] -> E arg exp r
case_ = ECase

unpair :: (In a, In b) => A arg (a,b) -> (A arg a -> A arg b -> E arg exp r) -> E arg exp r
unpair = EUnPair

unpairC :: (In a, In b) => A arg (a,b) -> C arg exp r (A arg a, A arg b)
unpairC x = cont $ \k -> EUnPair x (curry k)

(<?) :: E arg exp D -> E arg exp D -> E arg exp D
(<?) = EBChoice

infixr 4 <?

type C arg exp r a = Cont (E arg exp r) a 

unC :: C arg exp r (E arg exp r) -> E arg exp r
unC x = runCont x id 

call :: exp t -> E arg exp t
call = EVar 

mrec :: TypeList ts => (Apps exp ts -> Apps (E arg exp) ts) -> C arg exp r (Apps (E arg exp) ts)
mrec f = cont $ \k -> EMRec f (k . mapApps EVar)


fix1 :: (exp t -> E arg exp t) -> E arg exp t
fix1 f = runCont (mrec (\(t :> End) -> (f t :> End))) k
  where
    k :: Apps (E arg exp) '[a] -> E arg exp a
    k (t :> End) = t

fix2 :: ( (exp a, exp b) -> (E arg exp a, E arg exp b)) -> C arg exp r (E arg exp a, E arg exp b)
fix2 f = fmap toPair $ mrec (fromPair . f . toPair)
  where
    fromPair :: forall exp a b. (exp a,exp b) -> Apps exp '[a,b]
    fromPair (a,b) = a :> (b :> End)

    toPair :: forall exp a b. Apps exp '[a,b] -> (exp a, exp b)
    toPair (a :> b :> End) = (a,b)

fix3 :: ( (exp a, exp b, exp c) -> (E arg exp a, E arg exp b , E arg exp c) ) ->
        C arg exp r (E arg exp a, E arg exp b , E arg exp c)
fix3 f = fmap toTriple $ mrec (fromTriple . f  . toTriple )

toTriple :: Apps exp '[a,b,c] -> (exp a, exp b, exp c) 
toTriple (a :> b :> c :> End) = (a,b,c)

fromTriple (a,b,c) = a :> b :> c :> End 

fixs :: forall ts a arg exp r. Proxy ts ->
        (FromList a exp ts, FromList a (E arg exp) ts)
        => ([exp a] -> [E arg exp a]) -> C arg exp r [E arg exp a]
fixs _ f = fmap (fromJust . appsToList) $ mrec (fromJust . appsFromList . f . appsToList')
  where
    fromJust (Just x) = x
    fromJust _        = error "fromJust @ fixs: []"

    appsToList' a = fromJust (appsToList (a :: Apps exp ts ))

-- fixfix :: (TypeList ts, TypeList ts', TypeList (Append ts ts')) => 
--           (Apps exp ts -> Apps exp ts' -> Apps (E arg exp) ts) -> 
--           (Apps exp ts -> Apps exp ts' -> Apps (E arg exp) ts') ->
--           C arg exp r (Apps (E arg exp) ts,  Apps (E arg exp) ts')
-- fixfix f1 f2 =
--   fmap splitApps $   
--   mrec (\z -> let (a,b) = splitApps z
--               in appendApps (f1 a b) (f2 a b))

  
hardcat :: E arg exp D -> E arg exp D -> E arg exp D
hardcat = ECat

instance (D ~ t) => D.DocLike (E arg exp t) where
  text s = EText s
  empty  = EEmpty 

  (<>) x y  = x `ECat` (spaces `ECat` y)
  (<+>) x y = x `ECat` text " " `ECat` spaces `ECat` y 

  line      = ELine
  linebreak = ELineBreak

  align   = EAlign
  nest    = ENest
  group   = EGroup


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


varArg x = Printing $ \_ _ _ -> pprVName x

type Prec = Rational
data Printing d (t :: k) = Printing { unPrinting :: FCount -> VCount ->  Prec -> d }

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

instance FliPprC (Printing D.Doc) (Printing D.Doc) where
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
      (unPrinting x fn vn 10) D.</>
      D.nest 2 (D.group (D.text "[" D.<> D.align (D.punctuate (D.text "," D.<> D.line) ds D.<> D.text "]")))
      where
        pprBranch fn vn (Branch (PInv s _ _) f) = 
          let d = unPrinting (f (varArg (vn+1))) fn (vn+1) 0
          in D.text s D.<+>
             D.text "`Branch`" D.<+> D.align (D.text "\\" D.<> pprVName (vn+1) D.<+> D.text "->" D.<+> d)

  funpair x f = Printing $ \fn vn k -> 
    let d = unPrinting (f (varArg (vn+1)) (varArg (vn+2))) fn (vn+2) 1
    in parensIf (k > 1) $
       D.text "unpair" D.<+> (unPrinting x fn vn 10) D.<+> 
       D.text "$" D.<+> D.text "\\" D.<> pprVName (vn+1) D.<+> pprVName (vn+2) D.<+> D.text "->" D.<>
       D.nest 2 (D.line D.<> d)
     
  ftext s = Printing $ \fn vn k -> 
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

  ffix :: forall ts t. TypeList ts =>
          (Apps (Printing D.Doc) ts -> Apps (Printing D.Doc) ts)
          -> (Apps (Printing D.Doc) ts -> Printing D.Doc t) -> Printing D.Doc t 
  ffix f cont = Printing $ \fn vn k -> 
    let p = Proxy :: Proxy ts 
        vars = appsInit p (fn+1) (\fn' -> (Printing $ \_ _ _ -> pprFName fn', fn'+1))
        r = f vars
        fn' = fn + appsLength p 
        rest = unPrinting (cont vars) fn' vn 0 
    in parensIf (k > 9) $
       D.group $ D.align $ D.nest 2 $ D.text "ffix" D.</>
       parens (D.text "\\" D.<> parens (makeCons fn vn vars) D.<+> D.text "->" D.<+> parens (makeCons fn' vn r)) D.</>
       parens (D.text "\\" D.<> parens (makeCons fn vn vars) D.<+> D.text "->" D.<+> rest)
    where
      makeCons :: TypeList ks => FCount -> VCount -> Apps (Printing D.Doc) ks -> D.Doc
      makeCons fn vn =
        foldrApps (\a r -> unPrinting a fn vn 5 D.<+> D.text ":>" D.<+> r)
                  (D.text "End")
        -- concatMapApps (\a -> unPrinting a fn vn 5)
        --                  (D.text "End")
        --                  (\d1 d2 -> d1 D.<+> D.text ":>" D.<+> d2)


      

  falign e = Printing $ \fn vn k -> 
    let d = unPrinting e fn vn 10
    in parensIf (k > 9) $ D.text "align" D.<+> D.align d 

  fgroup e = Printing $ \fn vn k -> 
    let d = unPrinting e fn vn 10
    in parensIf (k > 9) $ D.align (D.text "group" D.<> D.nest 2 (D.line D.<> D.align d ))

  fnest i e = Printing $ \fn vn k -> 
    let d = unPrinting e fn vn 10
    in parensIf (k > 9) $ D.text "nest" D.<+> D.ppr i D.<+> D.align d 

instance (arg ~ Printing D.Doc, exp ~ Printing D.Doc) => D.Pretty (E arg exp t) where
  pprPrec k e = unPrinting (compile e) 0 0 k 


instance D.Pretty (FliPpr t) where
  pprPrec k (FliPpr e) = unPrinting e 0 0 k

instance Show (FliPpr t) where
  show = show . ppr 


example1 = flippr $ unC $ do
  let manyParens d = fix1 (\m -> d <? parens (call m))

  let pprTF = arg $ \i -> manyParens $ case_ i
        [ unTrue  `Branch` \_ -> text "True",
          unFalse `Branch` \_ -> text "False" ]

  (ppr, ppr') <- fix2 $ \(ppr, ppr') ->
    let ppr_ = arg $ \x -> case_ x
              [ unNil `Branch` \_ -> text "[" <> text "]",
                unCons `Branch` \xx -> unC $ do
                  (a,x) <- unpairC xx
                  return $ brackets (call ppr' `app` a `app` x)]
        ppr'_ = arg $ \a -> arg $ \x -> case_ x
          [ unNil `Branch` \_ -> pprTF `app` a
              , unCons `Branch` \xx -> unC $ do
                  (b,x) <- unpairC xx
                  return $ pprTF `app` a <> text "," <> call ppr' `app` b `app` x]
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
  
    
