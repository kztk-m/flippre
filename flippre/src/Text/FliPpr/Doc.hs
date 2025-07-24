{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | This module implements Wadler's pretty-printing combinators.
--   We do not use the existing well-designed libraries because we want to make
--   pretty-printing combinators class methods, so that FliPpr programs can use
--   the combinators, with different meanings in forward and backward execution.
module Text.FliPpr.Doc (
  DocLike (..),
  hang,
  foldDoc,
  hcat,
  vcat,
  cat,
  hsep,
  vsep,
  sep,
  (<$$>),
  ($$),
  (</>),
  (//),
  punctuate,
  (<>),
  parens,
  braces,
  brackets,
  parensIf,
)
where

import Data.Semigroup ()

import Data.String (IsString (..))
import qualified Prettyprinter as PP

-- | A type class that provides pretty-printing combinators.
class (Semigroup d, IsString d) => DocLike d where
  text :: String -> d
  text = fromString

  empty :: d
  empty = text ""

  (<+>) :: d -> d -> d
  x <+> y = x <> text " " <> y
  infixr 5 <+>

  line :: d

  -- represents nonempty spaces in parsing
  linebreak :: d

  -- represents arbitrary numbers of spaces in parsing

  align :: d -> d

  -- inspired by
  -- https://hackage.haskell.org/package/wl-pprint-1.2/docs/Text-PrettyPrint-Leijen.html#v:align

  nest :: Int -> d -> d

  -- will be ignored in parsing
  group :: d -> d

hang :: (DocLike d) => Int -> d -> d -> d
hang n x y = group (nest n (x $$ y))

($$) :: (DocLike d) => d -> d -> d
x $$ y = align (x <> linebreak <> y)

(<$$>) :: (DocLike d) => d -> d -> d
x <$$> y = x <> linebreak <> y

(</>) :: (DocLike d) => d -> d -> d
x </> y = x <> line <> y

(//) :: (DocLike d) => d -> d -> d
x // y = align (x <> line <> y)

infixr 5 <$$>

infixr 5 $$

infixr 5 </>

infixr 5 //

foldDoc :: (DocLike d) => (d -> d -> d) -> [d] -> d
foldDoc _ [] = empty
foldDoc _ [d] = d
foldDoc f (d : ds) = f d (foldDoc f ds)

hcat :: (DocLike d) => [d] -> d
hcat = foldDoc (<>)

vcat :: (DocLike d) => [d] -> d
vcat = foldDoc ($$)

cat :: (DocLike d) => [d] -> d
cat = group . vcat

vsep :: (DocLike d) => [d] -> d
vsep = foldDoc (</>)

hsep :: (DocLike d) => [d] -> d
hsep = foldDoc (<+>)

sep :: (DocLike d) => [d] -> d
sep = group . vsep

parens :: (DocLike d) => d -> d
parens d = text "(" <> d <> text ")"

brackets :: (DocLike d) => d -> d
brackets d = text "[" <> d <> text "]"

braces :: (DocLike d) => d -> d
braces d = text "{" <> d <> text "}"

parensIf :: (DocLike d) => Bool -> d -> d
parensIf True = parens
parensIf False = id

punctuate :: (DocLike d) => d -> [d] -> d
punctuate _op [] = empty
punctuate _op [d] = d
punctuate op (d : ds) = d <> op <> punctuate op ds

instance DocLike (PP.Doc ann) where
  line = PP.line
  linebreak = PP.line

  align = PP.align

  nest = PP.nest
  group = PP.group
