{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiWayIf                #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE UndecidableInstances      #-}

-- To suppress warnings caused by TH code.
{-# LANGUAGE MonoLocalBinds            #-}

import           Text.FliPpr
import qualified Text.FliPpr.Automaton     as AM

import qualified Text.FliPpr.Driver.Earley as E
import qualified Text.FliPpr.Grammar       as G

import           Data.String               (fromString)

import           Text.Printf

newtype Name = Name String
    deriving (Eq, Show)

data Lit = LBool Bool
         | LInt  Int
    deriving (Eq, Show)

data BinOp = Add | Mul
    deriving (Eq, Show)
data Exp
    = Op BinOp Exp Exp
    | Let Name Exp Exp
    | Literal Lit
    | If Exp Exp Exp
    | Var Name
    deriving (Eq, Show)

$(mkUn ''Name)
$(mkUn ''Exp)
$(mkUn ''Lit)


-- Compositional approach to pattern matching.
-- Can we do better by composing continuations (namely, br)?
newtype PatT env env' a = PatT { runPatT :: forall r. PartialBij r env -> PartialBij (a, r) env' }

varP :: PatT env (a, env) a
varP = PatT $ \(PartialBij s f fi) -> PartialBij ("_ " ++ s) (\(a,env) -> (a,) <$> f env) (\(a,r) -> (a,) <$> fi r)

lift :: forall a b env env'. PartialBij a b -> PatT env env' b -> PatT env env' a
lift (PartialBij fn f fi) (PatT tr) = PatT $ h . tr
    where
        h :: PartialBij (b, r) env' -> PartialBij (a, r) env'
        h (PartialBij gn g gi) = PartialBij (fn ++ "(" ++ gn ++ ")") (\(a,r) -> do { b <- f a; g (b, r) }) (\x -> do { (b, r) <- gi x; a <- fi b ; return (a, r) })
 --       (\x -> do { (b, r) <- g x; a <- f b ; return (a, r) }) (\(a,r) -> do { b <- f a; g (b, r) })

prod :: PatT env' env'' a -> PatT env env' b -> PatT env env'' (a, b)
prod (PatT tr1) (PatT tr2) = PatT $ \p -> arr (tr1 (tr2 p))
    where
        arr :: PartialBij (a, (b, r)) env'' -> PartialBij ((a, b), r) env''
        arr (PartialBij s f fi) = PartialBij s (f . (\((a,b),r) -> (a,(b,r))) ) (fmap (\(a, (b, r)) -> ((a, b), r)) . fi)

(&.) :: PatT env' env'' a -> PatT env env' b -> PatT env env'' (a, b)
(&.) = prod

infixr 4 &.

uni :: PartialBij a () -> PatT env env a
uni (PartialBij fn f fi) = PatT $ \(PartialBij gn g gi) -> PartialBij (fn ++ " " ++ gn) (\(a,r) -> do { env <- g r; () <- f a ; return env }) (\env -> (,) <$> fi () <*> gi env)

pOp :: PartialBij Exp (BinOp, (Exp, Exp))
pOp = PartialBij "Op" (\case { (Op b x1 x2) -> Just (b, (x1,x2)); _ -> Nothing }) (\(b, (x1,x2)) -> Just $ Op b x1 x2)

pMul :: PartialBij BinOp ()
pMul = PartialBij "Mul" (\case { Mul -> Just () ; _ -> Nothing}) (const $ Just Mul)

pat :: PatT () env a -> PartialBij a env
pat tr = h $ runPatT tr (PartialBij "" Just Just)
    where
        h :: PartialBij (a, ()) env -> PartialBij a env
        h (PartialBij fn f fi) = PartialBij fn (\a -> f (a, ())) (fmap fst . fi)

px :: PatT env (Exp, (Exp, (Exp, env))) Exp
px = lift pOp (uni pMul &. lift pOp (uni pMul &. varP &. varP) &. varP)

class FliPprE arg exp => Decomp arg exp a r t | r -> t exp arg, exp -> arg, exp a t -> r where
    decomp :: A arg a -> r -> E exp t

-- instance Decomp arg exp a (A arg a -> E exp t) t where
--     decomp a f = f a

instance (FliPprE arg exp) => Decomp arg exp () (E exp t) t where
    decomp a f = ununit a f

instance (Eq a, Eq as, Decomp arg exp as r t) => Decomp arg exp (a, as) (A arg a -> r) t where
    decomp as f = unpair as $ \a1 a2 -> decomp a2 $ f a1

br :: (Decomp arg exp b r t, Eq b) => PatT () b a -> r -> Branch (A arg) (E exp) a t
br p k = Branch (pat p) $ \a -> decomp a k

_btest = br px $ \_e1 _e2 _e3 -> text ""

{-

var :: Pat a a

var : forall env r. PInj env r -> PInj (a:env) (a, r)

var : PatT env (a : env) a


f : PInj a b
-------------------------------------------
lift f : PatT env env' b -> PatT env env' a

prod :: PatT env' env'' a -> PatT env env' b -> PatT env env'' (a, b)


PatT
var :: Pat env b -> Pat (a:env) (a, b)

f : PartialBij a b   p : Pat env b
--------------------------------------
f p : Pat env a


f : PartialBij a (b, c)   p : Pat env1 b   q : Pat env2 c
----------------------------------------------------------
f p1 p2 : Pat (env1 ++ env2) a

p : Pat [a1...an] a      k : A arg a1 ... A arg an -> E exp r
--------------------------------------------------------------
pat p : Branch (A arg) (E exp) r a


-}

otherwiseP :: (arg Exp -> exp t) -> Branch arg exp Exp t
otherwiseP = Branch (PartialBij "otherwiseP" Just Just)

-- since un* expressions do no compose well, we need to prepare some special combinators.
unOpAdd :: FliPprE arg exp => (A arg Exp -> A arg Exp -> E exp t) -> Branch (A arg) (E exp) Exp t
unOpAdd f = Branch (PartialBij "Op Add _ _"
                               (\case { Op Add e1 e2 -> Just (e1, e2); _ -> Nothing })
                               (\case { (e1, e2) -> Just (Op Add e1 e2) })) $ \e1e2 -> unpair e1e2 f

unOpMul :: FliPprE arg exp => (A arg Exp -> A arg Exp -> E exp t) -> Branch (A arg) (E exp) Exp t
unOpMul f = Branch (PartialBij "Op Mul _ _"
                               (\case { Op Mul e1 e2 -> Just (e1, e2); _ -> Nothing })
                               (\case { (e1, e2) -> Just (Op Add e1 e2) })) $ \e1e2 -> unpair e1e2 f

atoiP :: (arg String -> exp t) -> Branch arg exp Int t
atoiP = Branch (PartialBij "atoi"
                           (Just . show)
                           (\s -> l2m $ do { (n, "") <- reads s; return n }))
    where
        l2m []    = Nothing
        l2m (x:_) = Just x

number :: AM.DFA Char
number = AM.range '0' '9'

numbers :: AM.DFA Char
numbers = AM.plus number

ident :: AM.DFA Char
ident = (small <> AM.star alphaNum) `AM.difference` AM.unions (map fromString keywords)
    where
        small = AM.unions [AM.range 'a' 'z', AM.singleton '_']
        alphaNum = AM.unions [number, small, AM.range 'A' 'Z']

keywords :: [String]
keywords = [ "true", "false", "let", "in", "if", "then", "else" ]

flipprExp :: FliPprD arg exp => FliPprM exp (A arg Exp -> E exp D)
flipprExp = do
    pprName <- share $ \x -> case_ x [ unName $ \s -> textAs s ident ]
    pprInt  <- share $ \n -> case_ n [ atoiP $ \s -> textAs s numbers ]
    pprBool <- share $ \b -> case_ b [ unTrue $ text "true", unFalse $ text "false" ]

    let pprLet p n e1 e2 = group $
         vsep [ hsep [ text "let", pprName n <+>. text "=" <+>. align (p 0 e1) ],
                hsep [ text "in", align (p 0 e2) ] ]
    let pprIf p e0 e1 e2 = group $
            vsep [ hsep [ text "if", p 0 e0 ],
                   hsep [ text "then", p 0 e1 ],
                   hsep [ text "else", p 0 e2 ] ]
    let pprOp p (Fixity assoc prec) opS e1 e2 =
            let (dl, dr) | AssocL <- assoc = (0, 1)
                        | AssocR <- assoc = (1, 0)
                        | AssocN <- assoc = (1, 1)
            in p (prec + dl) e1 <+>. text opS <+>. p (prec + dr) e2

    let pprVar = pprName
    let pprLit l = case_ l [ unLBool pprBool,
                             unLInt  pprInt ]

    -- Technique mentioned in http://www.haskellforall.com/2020/11/pretty-print-syntax-trees-with-this-one.html.
    -- A trick is that patterns are intentionally overlapping, so that it can parse ugly string, wihtout <?
    letrs [0..3] $ \pExp ->
        def (\prec x ->
            if | prec == 0 ->
                case_ x [ unLet $ \n e1 e2  -> pprLet pExp n e1 e2,
                          unIf  $ \e0 e1 e2 -> pprIf pExp e0 e1 e2,
                          otherwiseP $ pExp (prec + 1) ]
               | prec == 1 ->
                case_ x [ $(branch [p| Op Add e1 e2 |] [| pprOp pExp (Fixity AssocL 1) "+" e1 e2 |]),
                          otherwiseP $ pExp (prec + 1) ]
               | prec == 2 ->
                   case_ x [ --  $(branch [p| Op Mul e1 e2 |] [| pprOp pExp (Fixity AssocL 2)  "*" e1 e2 |]),
                             -- compostional approach to pattern matching
                             br (lift pOp (uni pMul &. varP &. varP)) $ \e1 e2 -> pprOp pExp (Fixity AssocL 2) "*" e1 e2,
                             otherwiseP $ pExp (prec + 1) ]
               | otherwise ->
                   case_ x [ unVar $ \n -> pprVar n,
                             unLiteral $ \l -> pprLit l,
                             otherwiseP $ parens . pExp 0 ]) $
        return (pExp 0)

gExp :: G.GrammarD Char g => g (Err Exp)
gExp = parsingModeWith (CommentSpec (Just "--") (Just $ BlockCommentSpec "{-" "-}" True)) (flippr $ fromFunction <$> flipprExp)

parseExp :: [Char] -> Exp
parseExp = \s -> case p s of
    Ok r   -> head r
    Fail e -> error (show e)
    where
        -- This assignment is important; otherwise, gExp is evaluated again for calls of parseExp.
        p = E.parse gExp

pprExp :: Exp -> Doc
pprExp = pprMode (flippr $ fromFunction <$> flipprExp)

exp1 :: Exp
exp1 =
    Let x (Op Mul (Literal $ LInt 5) (Op Add (Literal $ LInt 3) (Literal $ LInt 4))) $
    Let y (If (Literal $ LBool True) (Literal $ LBool False) (Literal $ LBool False)) $
    If (Var y) (Var x) (Literal $ LInt 0)
        where
            x = Name "x"
            y = Name "y"

main :: IO ()
main = do
    let s = render 80 (pprExp exp1)
    putStrLn "`pprExp exp1` results in ..."
    putStrLn s
    let e = parseExp s
    putStrLn $ replicate 80 '-'
    putStrLn "`parseExp (pprExp exp1)` results in ..."
    print e
    putStrLn $ replicate 80 '-'
    printf "`exp1 == parseExp (pprExp exp1)` = %s\n" (show $ e == exp1)
