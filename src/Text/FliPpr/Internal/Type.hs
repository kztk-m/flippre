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

module Text.FliPpr.Internal.Type where

import Data.Kind 
import Data.Coerce
import Control.Monad ((>=>), ap)
import Control.Monad.Fix (MonadFix(..))

import Data.Functor.Identity 

import Text.FliPpr.Doc as D 

data FType = D | Type :~> FType 

data Branch arg exp a (t :: FType) =
  forall b. Branch (a <-> b) (arg b -> exp t)

data a <-> b = PInv (a -> Maybe b) (b -> Maybe a) 


class FliPprE (arg :: * -> *) (exp :: FType -> *) | exp -> arg where
  app   :: exp (a :~> t) -> arg a -> exp t
  arg   :: (arg a -> exp t) -> exp (a :~> t)

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
  ffix  :: (exp t -> exp t) -> exp t

  case_  :: arg a -> [Branch arg exp a t] -> exp t 
  unpair :: arg (a,b) -> (arg a -> arg b -> exp t) -> exp t

  (<?)   :: exp D -> exp D -> exp D

  ftext  :: String -> exp D
  fempty :: exp D
  fcat   :: exp D -> exp D -> exp D

  -- For optimization purpose.
  fspaces    :: exp D
  fline      :: exp D -- translated to @text " " <> spaces@ in parsing 
  flinebreak :: exp D -- translated to @spaces@ in parsing

  falign :: exp D -> exp D
  fgroup :: exp D -> exp D
  fnest  :: Int -> exp D -> exp D

spaces :: FliPprE arg exp => exp D 
spaces = fspaces

instance (D ~ t, FliPprE arg exp) => D.DocLike (exp t) where
  text  = ftext
  empty = fempty

  (<>) x y  = x `fcat` (spaces `fcat` y)
  (<+>) x y = x `fcat` ftext " " `fcat` spaces `fcat` y 

  line = fline
  linebreak = flinebreak 

  align = falign
  nest  = fnest
  group = fgroup   

class (FliPprE arg exp, MonadFix r) => FliPpr arg exp r where
  rule :: exp t -> r (exp t)


class Fix a where
  fix :: (a -> a) -> a

instance FliPprE arg exp => Fix (exp a) where
  fix = ffix

instance Fix () where
  fix _ = ()

instance (Fix a, Fix b) => Fix (a,b) where
  fix f = 
    (fix (\z -> fst (f (z, fix (\w -> snd (f (z,w)))))),
     fix (\z -> snd (f (fix (\w -> fst (f (w,z))), z))))

instance (Fix a, Fix b) => Fix (a :> b) where
  fix f =
    (fix (\z -> fst (f (z :> fix (\w -> snd (f (z :> w)))))))
    :>
    (fix (\z -> snd (f (fix (\w -> fst (f (w :> z))) :> z))))
    where
      fst (a :> _) = a
      snd (_ :> b) = b 

data E = E 
data a :> b = a :> b

infixr 1 :>

type Prec = Rational 
type NameSource = Int 
data Printing d (t :: k) = Printing { unPrinting :: NameSource -> Prec -> d }

data Assoc = AssocL | AssocR | NonAssoc 

parensIf :: D.DocLike d => Bool -> d -> d
parensIf True  d = D.text "(" D.<> d D.<> D.text ")"
parensIf False d = d

opPrinter :: D.DocLike d =>  Assoc -> d -> Prec -> (Prec -> d) -> (Prec -> d) ->  Prec -> d
opPrinter a d opK pprx ppry k =
  parensIf (k > opK) $ pprx (opK + dx) D.<> d D.<> ppry (opK + dy) 
  where
    (dx, dy) = case a of
                 AssocL   -> (0, 1)
                 AssocR   -> (1, 0)
                 NonAssoc -> (1, 1)               


prefixPrinter :: D.DocLike d => Assoc -> [(d, Prec -> d)] -> Maybe d -> Prec -> d
prefixPrinter a ds trailing k =
  parensIf (k > 0) $
    case trailing of
      Just t  -> go t 0 ds
      Nothing -> go D.empty (case a of { AssocR -> 0; _ -> 1 }) ds
  where
    go t n []      = t
    go t n [(d,f)] = d D.<> f n D.<> t
    go t n ((d,f):ds) =
      d D.<> f 0 D.<> go t n ds 
    



varName :: D.DocLike d => NameSource -> d 
varName n | n < length fancyNames = D.text [fancyNames !! n]
          | otherwise             = D.text ("x" ++ show n)
  where
    fancyNames = "xyzwsturabcdeijklmnpqv"

var :: D.DocLike d => NameSource -> Printing d (t :: k)
var n = Printing $ \_ _ -> varName n 

pprArr :: D.DocLike d => d -> (Prec -> d) -> d
pprArr d1 d2 = D.text "\\" D.<> d1 D.<+> D.text "->" D.<+> D.align (d2 0)

arr :: D.DocLike d => (Printing d a -> Printing d t) -> Printing d t'
arr f = Printing $ \n k -> parensIf (k > 1) $ 
         pprArr (varName n) (unPrinting (f $ var n) (n+1))
               
instance D.DocLike d => FliPprE (Printing d) (Printing d) where
  app (Printing f) (Printing g) =
    Printing $ \n -> D.group .
                      opPrinter AssocL (D.text " ") 9
                       (f n) (D.nest 2 . (D.linebreak D.<>) . D.align . g n)

  arg f =
    Printing $ \n k ->
       parensIf (k > 1) $
         group (text "arg" <+> text "$" //
                  nest 2 (unPrinting (arr f) n 1))

         
       -- opPrinter AssocL (D.text " ") 9
       --   (\_ -> D.text "arg")
       --   (unPrinting (arr f) n)

  ffix f = Printing $ \n ->
    opPrinter AssocL (D.text " ") 9
       (\_ -> D.text "ffix")
       (unPrinting (arr f) n)

  case_ (Printing x) bs = Printing $ \n k ->
    (parensIf (k > 0) $ D.text "case_" D.<+> x n 0 D.<+> D.group (D.text "[" D.<> D.align (go n bs D.<> D.text "]")))
     where
       go n []     = D.empty 
       go n [b]    = pprBranch n b
       go n (b:bs) = pprBranch n b D.<> D.text "," D.<> D.line D.<> go n bs

       pprBranch n (Branch (PInv f g) h) =
         unPrinting (h (var n)) (n+1) 0

  unpair (Printing p) f = Printing $ \n k ->
    let v1 = var n
        v2 = var (n+1)
    in parensIf (k > 10) $ D.text "unpair" D.<+> p n 9 D.<+> unPrinting (f v1 v2) (n+2) 9

  Printing f <? Printing g = Printing $ \n ->
    opPrinter AssocR (D.text "<?") 4 (f n) (g n)

  fempty  = Printing $ \_ _ -> D.text "fempty" 
  ftext s = Printing $ \_ _ -> D.text "ftext" D.<+> D.text (show s)

  Printing f `fcat` Printing g =
    Printing $ \n -> opPrinter AssocR (D.text " " <> D.text "<>" <> D.text " ") 5 (f n) (D.align . g n)

  fline = Printing $ \_ _ -> D.text "fline"
  flinebreak = Printing $ \_ _ -> D.text "flinebreak"

  falign (Printing f) =
    Printing $ \n -> opPrinter AssocL (D.text " ") 9
                       (const $ D.text "falign") (D.align . f n)

  fnest i (Printing f) =
    Printing $ \n -> D.group . opPrinter AssocL (D.text " ") 9
                 (const $ D.text "fnest" D.<+> D.text (show i))
                 (D.align . f n)
                                          
  fgroup (Printing f) =
    Printing $ \n -> D.group . opPrinter AssocL (D.text " ") 9
                            (const $ D.text "fgroup")
                            (D.nest 2 . (D.linebreak D.<> ) . D.align . f n)

  fspaces =
    Printing $ \_ _ -> D.text "fspaces"


instance D.DocLike d => FliPpr (Printing d) (Printing d) Identity where
  rule = Identity

instance D.Pretty (Printing D.Doc t) where
  pprPrec k (Printing f) = f 0 k 


pprMono :: DocLike d => Printing d (t :: FType) -> d
pprMono f = unPrinting f 0 0 

pprExp :: forall (t :: FType). (forall arg exp. FliPprE arg exp => exp t) -> D.Doc
pprExp e = D.ppr (e :: Printing D.Doc t)
  
ppr :: forall (t :: FType). (forall arg exp r. FliPpr arg exp r => r (exp t)) -> D.Doc
ppr e = pprMono (runIdentity e)

  
-- data Decl e a =
--   Decl { unDecl :: forall t.
--             (forall y. (y -> t y)) ->
--             (forall y z. t y -> (y -> t z) -> t z) -> 
--             ((forall y. (y -> t y) -> t y) -> (t a)) }


-- instance Functor (Decl e)  where
--   fmap f (Decl m) = Decl (\ret b fx -> m ret b fx `b` (\z -> ret (f z)))

-- instance Applicative (Decl e) where
--   pure = return
--   (<*>) = ap 

-- instance Monad (Decl e) where
--   return x = Decl (\ret b _ -> ret x)
--   Decl k >>= f =
--     Decl (\ret b fx -> k ret b fx `b` (\r -> unDecl (f r) ret b fx))

-- instance MonadFix (Decl e) where
--   mfix h = Decl (\ret b fx -> fx (\z -> unDecl (h z) ret b fx) )

-- newtype I a = I a 

-- data R :: * -> * where
--   R :: a -> R (I a)
--   B :: R a -> R b -> R (a,b)

-- bindR :: R a -> (a -> R b) -> R b
-- bindR (R a) f = f (coerce a)
-- bindR (B x y) f = x `bindR` (\a -> y `bindR` (\b -> f (a, b)))


-- data Decl m e a =  Decl { unDecl :: (forall t. e t -> m (e t)) -> m a }

-- instance Functor m => Functor (Decl m e) where
--   fmap f (Decl h) = Decl (\k -> fmap f (h k))

-- instance Applicative m => Applicative (Decl m e) where
--   pure a = Decl (\_ -> pure a)
--   Decl f <*> Decl x = Decl (\k -> f k <*> x k)

-- instance Monad m => Monad (Decl m e) where
--   return = pure
--   Decl f >>= k = Decl (\d -> f d >>= \x -> unDecl (k x) d )

-- instance MonadFix m => MonadFix (Decl m e) where
--   mfix f = Decl (\d -> mfix (\x -> unDecl (f x) d))

-- decl :: e t -> Decl m e (e t)
-- decl x = Decl (\d -> d x)

-- data Proxy a = Proxy 

-- data Rep t where
--   RepNil  :: Rep ()
--   RepCons :: Proxy a -> Rep n -> Rep (a , n) 

-- data In a t where
--   RZ :: In a (t , a)
--   RS :: In a t -> In a (t, b) 

     
  
--   DeclD :: F arg e => e t -> (e t -> Decl e a) -> Decl e a
--   DeclR :: a -> Decl e a
--   DeclF :: (z -> Decl e z) -> (z -> Decl e a) -> Decl e a

-- instance Functor (Decl e) where
--   fmap f (DeclD e k) = DeclD e (fmap f . k)
--   fmap f (DeclR a)   = DeclR (f a)
--   fmap f (DeclF e k) = DeclF e (fmap f . k)

-- instance Applicative (Decl e) where
--   pure = return
--   (<*>) = ap

-- instance Monad (Decl e) where
--   return = DeclR
--   DeclD e k >>= f = DeclD e (k >=> f)
--   DeclR a >>= f   = f a
--   DeclF h k >>= f = DeclF h (k >=> f)


-- data Rep t where
--   RepNil  :: Rep ()
--   RepCons :: Proxy a -> Rep n -> Rep (a , n) 

-- data In a t where
--   RZ :: In a (t , a)
--   RS :: In a t -> In a (t, b) 
  
-- data M s a = M { unM :: forall tenv. Rep tenv -> ST s a }

-- runDecl :: a -> (STRef s Int -> ST s (a, Int))
-- runDecl body = \r -> do
--   i <- readSTRef r
--   writeSTRef r (i+1)
--   return (body, i)

  
           
    
                    



  


