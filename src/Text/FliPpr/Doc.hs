{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Text.FliPpr.Doc (
  Precedence, Pretty(..), DocLike(..), Renderable(..), 
  pretty, Doc,

  hang, foldDoc, 
  hcat, vcat, cat,
  hsep, vsep, sep, 
  (<$$>), ($$), (</>), (//),
  punctuate,  (<>), 

  parens, braces, brackets, parensIf,

  ) where

import Control.Arrow (second) 
import Data.Monoid (Monoid(..))
import Data.Semigroup 
import Data.Coerce

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

instance Pretty Bool where ppr = text . show 
instance Pretty Int where ppr = text . show
instance Pretty Integer where ppr = text . show
instance Pretty Char where
  ppr = text . show
  pprList = text . show 
instance Pretty Float where ppr = text . show
instance Pretty Double where ppr = text . show

class (Semigroup d, Monoid d) => DocLike d where
  text  :: String -> d
  empty :: d 
  empty = mempty 

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

(<$$>) :: DocLike d => d -> d -> d
x <$$> y = x <> linebreak <> y 

(</>) :: DocLike d => d -> d -> d
x </> y = x <> line <> y 

(//) :: DocLike d => d -> d -> d
x // y = align (x <> line <> y)

infixr 5 <$$> 
infixr 5 $$  
infixr 5 </> 
infixr 5 //  

foldDoc :: DocLike d => (d -> d -> d) -> [d] -> d 
foldDoc _ []     = empty
foldDoc _ [d]    = d
foldDoc f (d:ds) = f d (foldDoc f ds)
  
hcat :: DocLike d => [d] -> d
hcat = foldDoc (<>) 

vcat :: DocLike d => [d] -> d
vcat = foldDoc ($$) 

cat :: DocLike d => [d] -> d 
cat = group . vcat 

vsep :: DocLike d => [d] -> d
vsep = foldDoc (</>)

hsep :: DocLike d => [d] -> d
hsep = foldDoc (</>)

sep :: DocLike d => [d] -> d
sep = group . vsep

parens :: DocLike d => d -> d
parens d = text "(" <> d <> text ")"

brackets :: DocLike d => d -> d
brackets d = text "[" <> d <> text "]"

braces :: DocLike d => d -> d
braces d = text "{" <> d <> text "}"


parensIf :: DocLike d => Bool -> d -> d
parensIf True  = parens
parensIf False = id 

punctuate :: DocLike d => d -> [d] -> d
punctuate _sep []  = empty
punctuate _sep [d] = d
punctuate sep (d:ds) = d <> sep <> punctuate sep ds 

class DocLike d => Renderable d where
  render  :: Width -> d -> String
  render w d = renders w d ""
  
  renders :: Width -> d -> ShowS 

pretty :: Renderable d => d -> String
pretty = render 80

prettys :: Renderable d => d -> ShowS
prettys = renders 80 

type Width     = Int
newtype Indent = Indent Int deriving (Show,Num) -- Indent level 
type Pos       = Int -- Current position 
type Remaining = Int 
newtype Col    = Col Int deriving (Show,Num) -- Actual Column
data Mode = Horizontal | Vertical 

{-
Shallow embedding presentation of Wadler's combiantors 
taken from Section 2 of
 D. W. Swierstra & O. Chitil.
 Linear, bounded, functional pretty-printing, JFP 19 (1), 2009.
-}
newtype WSpec =
  WSpec (Mode -> Width -> Pos -> Indent -> Remaining -> Col -> (ShowS, Pos, Remaining, Col))

instance Semigroup WSpec where
  WSpec d1 <> WSpec d2 = WSpec $ \m w p i r c -> 
    let (l1, p1, r1, c1) = d1 m w p  i r c 
        (l2, p2, r2, c2) = d2 m w p1 i r1 c1
    in (l1 . l2, p2, r2, c2)

instance Monoid WSpec where
  mempty  = WSpec $ \_m _w p _i r c -> (showString "", p , r, c )
  mappend = (<>) 

instance DocLike WSpec where
  text s = WSpec $ \_m _w p _i r c -> (showString s,  p + len, r - len , c + coerce len)
    where
      len = length s 

  group (WSpec d) = WSpec $ \_ w p i r c ->
    let v@(_, pd, _, _) = d (if pd - p <= r then Horizontal else Vertical) w p i r c in v

  nest n (WSpec d) = WSpec $ \m w p i -> d m w p (i+coerce n)
  align (WSpec d) = WSpec $ \m w p _ r c -> d m w p (coerce c) r c
  line = WSpec $ \m w p i r c ->
                   let (l, r', c') = makeLine m w i r c
                   in (l, p+1, r', c')
    where
      makeLine :: Mode -> Width -> Indent -> Remaining -> Col -> (ShowS, Remaining, Col)
      makeLine Horizontal _  _i  r  c = (showString " ", r - 1, c + 1)
      makeLine Vertical   w  i  _r _c = (showString ('\n':replicate i' ' '), w - i', coerce i)
        where i' = coerce i
          

  linebreak = WSpec $ \m w p i r c ->
                    let (l, r', c') = makeBreak m w i r c
                    in (l, p, r', c')
    where
      makeBreak :: Mode -> Width -> Indent -> Remaining -> Col -> (ShowS, Remaining, Col) 
      makeBreak Horizontal _ _i r c = (showString "", r, c)
      makeBreak Vertical   w  i _ _ = (showString ('\n':replicate i' ' '), w - i', coerce i)
        where i' = coerce i 
      

instance Renderable WSpec where
  renders w (WSpec d) =
    let (l,_,_,_) = d Vertical w 0 0 w 0
    in l 

-- FIXME: Norm does not normalize after @align@
newtype Norm d = Norm { unNorm :: d -> (d,d) }

instance DocLike d => Semigroup (Norm d) where
  Norm f1 <> Norm f2 = Norm $ \d ->
    let (td1, sd1) = f1 td2
        (td2, sd2) = f2 d 
    in (td1 , sd1 <> sd2)

instance DocLike d => Monoid (Norm d) where
  mempty  = Norm $ \d -> (d, empty)
  mappend = (<>) 

instance DocLike d => DocLike (Norm d) where
  text t = Norm $ \d -> (text t <> d, empty)
  line   = Norm $ \d -> (empty, line <> d)
  linebreak = Norm $ \d -> (empty, linebreak <> d)

  group d = Norm $ \dd -> second group (unNorm d dd)
  nest n d = Norm $ \dd -> second (nest n) (unNorm d dd)
  align d = Norm $ \dd -> let (d1, d2) = unNorm d dd
                          in (empty, align (d1 <> d2))

instance Renderable d => Renderable (Norm d) where
  renders w (Norm f) = let (td, sd) = f empty
                       in renders w (td <> sd)

newtype Doc = Doc (Norm WSpec) deriving (Semigroup, Monoid, DocLike, Renderable) 
instance Show Doc where
  showsPrec _ = prettys 

