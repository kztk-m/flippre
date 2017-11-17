{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Text.FliPpr.Doc where

import Control.Arrow (second) 

type Precedence = Rational 

class Pretty a where
  pprPrec :: Precedence -> a -> Doc
  pprPrec _ = ppr 

  ppr     :: a -> Doc
  ppr = pprPrec 0 

  pprList :: [a] -> Doc
  pprList = brackets . punctuate (text ",") . map ppr
    where
      brackets d = group (text "[" <> align (d </> text "]"))


instance Pretty a => Pretty [a] where
  ppr = pprList 

instance Pretty Int where ppr = text . show
instance Pretty Integer where ppr = text . show
instance Pretty Char where
  ppr = text . show
  pprList = text . show 
instance Pretty Float where ppr = text . show
instance Pretty Double where ppr = text . show

class DocLike d where
  text  :: String -> d
  empty :: d 

  (<>)  :: d -> d -> d
  infixr 5 <>

  (<+>) :: d -> d -> d
  x <+> y = x <> text " " <> y 
  infixr 5 <+>

  line  :: d
    -- represents nonempty spaces in parsing 
  linebreak :: d 
    -- represents arbitrary numbers of spaces in parsing

  align :: d -> d
    -- inspired by
    -- https://hackage.haskell.org/package/wl-pprint-1.2/docs/Text-PrettyPrint-Leijen.html#v:align

  nest  :: Int -> d -> d
    -- will be ignored in parsing
  group :: d -> d
    -- will be ignored in parsing 

hang :: DocLike d => Int -> d -> d -> d
hang n x y = group (nest n (x $$ y))

($$) :: DocLike d => d -> d -> d 
x $$ y = align (x <> linebreak <> y)

(<$>) :: DocLike d => d -> d -> d
x <$> y = x <> linebreak <> y 

(</>) :: DocLike d => d -> d -> d
x </> y = x <> line <> y 

(//) :: DocLike d => d -> d -> d
x // y = align (x <> line <> y)

infixr 5 <$> 
infixr 5 $$  
infixr 5 </> 
infixr 5 //  

hcat :: DocLike d => [d] -> d
hcat = foldr (<>) empty

vcat :: DocLike d => [d] -> d
vcat = foldr ($$) empty

cat :: DocLike d => [d] -> d 
cat = group . vcat 

vsep :: DocLike d => [d] -> d
vsep = foldr (</>) empty

hsep :: DocLike d => [d] -> d
hsep = foldr (<+>) empty 

sep :: DocLike d => [d] -> d
sep = group . vsep

punctuate :: DocLike d => d -> [d] -> d
punctuate sep []  = empty
punctuate sep [d] = d
punctuate sep (d:ds) = d <> sep <> punctuate sep ds 

class DocLike d => Renderable d where
  render :: Width -> d -> String

pretty :: Renderable d => d -> String
pretty = render 80

type Width     = Int
type Indent    = Int -- Indent level 
type Pos       = Int -- Current position 
type Remaining = Int 

data Mode = Horizontal | Vertical 

{-
Shallow embedding presentation of Wadler's combiantors 
taken from Section 2 of
 D. W. Swierstra & O. Chitil.
 Linear, bounded, functional pretty-printing, JFP 19 (1), 2009.
-}
newtype WSpec =
  WSpec { unWSpec :: Mode -> Width -> Pos -> Indent -> Remaining -> (ShowS, Pos, Remaining) }

instance DocLike WSpec where
  empty  = WSpec $ \m w p i r -> (showString "", p , r)
  text s = WSpec $ \m w p i r -> (showString s, p + length s, r - length s)
  (WSpec d1) <> (WSpec d2) = WSpec $ \m w  p i r ->
    let (l1, p1, r1) = d1 m w p  i r
        (l2, p2, r2) = d2 m w p1 i r1 
    in (l1 . l2, p2, r2)
  group (WSpec d) = WSpec $ \m w p i r ->
    let v@(_, pd, _) = d (if pd - p <= r then Horizontal else Vertical) w p i r in v

  nest n (WSpec d) = WSpec $ \m w p i -> d m w p (i+n)
  align (WSpec d) = WSpec $ \m w p i -> d m w p p 
  line = WSpec $ \m w p i r ->
                   let (l, r') = makeLine m w i r 
                   in (l, p+1, r)
    where
      makeLine Horizontal _  i r = (showString " ", r - 1)
      makeLine Vertical   w  i r = (showString ('\n':replicate i ' '), w - i)

  linebreak = WSpec $ \m w p i  r ->
                    let (l, r') = makeBreak m w i r
                    in (l, p, r)
    where
      makeBreak Horizontal _ i r = (showString "", r)
      makeBreak Vertical   w i _ = (showString ('\n':replicate i ' '), w - i)
      

instance Renderable WSpec where
  render w (WSpec d) =
    let (l,_,_) = d Vertical w 0 0 w
    in l ""

newtype Norm d = Norm { unNorm :: d -> (d,d) }

instance DocLike d => DocLike (Norm d) where
  empty  = Norm $ \d -> (d, empty)
  text t = Norm $ \d -> (text t <> d, empty)
  line   = Norm $ \d -> (empty, line <> d)
  linebreak = Norm $ \d -> (empty, linebreak <> d)
  (Norm f1) <> (Norm f2) = Norm $ \d ->
    let (td1, sd1) = f1 td2
        (td2, sd2) = f2 d 
    in (td1 , sd1 <> sd2)
  group d = Norm $ \dd -> second group (unNorm d dd)
  nest n d = Norm $ \dd -> second (nest n) (unNorm d dd)
  align d = Norm $ \dd -> second (align) (unNorm d dd) -- right? 

instance Renderable d => Renderable (Norm d) where
  render w (Norm f) = let (td, sd) = f empty
                      in render w (td <> sd)

newtype Doc = Doc (Norm WSpec) deriving (DocLike, Renderable) 
instance Show Doc where show = pretty 
