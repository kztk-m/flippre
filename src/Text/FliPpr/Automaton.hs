{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module Text.FliPpr.Automaton
    (
        DFA, DFAImpl(..), NFA(..), NFANE(..), Regex(..), range, plus, intersections, unions,
    )
    where

import           Data.RangeSet.List   (RSet)
import qualified Data.RangeSet.List   as RS


import           Data.Function        (on)
import qualified Data.Graph           as Graph
import qualified Data.List            as L
import qualified Data.Map             as M
import           Data.Maybe           (fromJust, fromMaybe)
import qualified Data.Set             as S


import           Data.String          (IsString (..))

import           Control.Arrow        (second)
import           Control.Monad.Writer
import           Data.Bifunctor       (bimap)

import           Text.FliPpr.Doc      as D hiding (empty)

-- import           Debug.Trace


data NFANE c q =
    NFANE { initsNFAne  :: S.Set q, -- ^ Initial state,
            finalsNFAne :: S.Set q, -- ^ final state
            transNFAne  :: M.Map q [(RSet c, q)] }

pprRSet :: (Eq c, Show c) => RSet c -> D.Doc
pprRSet = D.brackets . go . RS.toRangeList
    where
        go []     = mempty
        go ((a,a'):r)
            | a == a'   = D.text (show a) D.<> go r
            | otherwise = D.text (show a) D.<> D.text "-" D.<> D.text (show a') D.<> go r


pprTr :: (Show q, Eq c, Show c) => [(q, [(RSet c, q)])] -> D.Doc
pprTr = D.punctuate (D.text ";" <> D.line) . map (\(q, dsts) ->
            D.hsep[ D.text (show q), D.text "->", D.group $ D.align $ D.punctuate (D.line D.<> D.text "|" D.<+> mempty) $ map (\(cs,q') -> D.hsep [pprRSet cs, D.text (show q')] ) dsts ])

pprTrMap :: (Show q, Eq c, Show c) => M.Map q [(RSet c, q)] -> D.Doc
pprTrMap = pprTr . M.toList

instance (Show q, Eq c, Show c) => D.Pretty (NFANE c q) where
    ppr (NFANE is fs tr) =
        D.vsep [ D.text "Initial(s):" D.<+> D.text (show is),
                 D.text "Final(s):  " D.<+> D.text (show fs),
                 D.vsep [D.text "Transition(s):", D.nest 2 (D.align (pprTrMap tr)) ]]

data NFA c q = NFA (NFANE c q) (M.Map q [q])

instance (Show q, Eq c, Show c) => D.Pretty (NFA c q) where
    ppr (NFA (NFANE is fs tr) eps) =
        D.vsep [ D.text "Initial(s):" D.<+> D.text (show is),
                 D.text "Final(s):  " D.<+> D.text (show fs),
                 D.vsep [D.text "Transition(s):", D.nest 2 (D.align (pprTrMap tr)) ],
                 D.vsep [D.text "Eps rule(s):", D.nest 2 (D.align (pprEps $ M.toList eps)) ]
                 ]
        where
            pprEps = D.vsep . map (\(q,qs) -> D.hsep [ D.text (show q), D.text "->", D.text (show qs) ])


type DFA c = DFAImpl c Word

data DFAImpl c q =
    DFAImpl { initDFAImpl :: q,
          statesDFAImpl   :: S.Set q,
          finalsDFAImpl   :: S.Set q,
          transDFAImpl    :: M.Map q [(RSet c, q)] }

instance (Show q, Eq c, Show c) => D.Pretty (DFAImpl c q) where
    ppr (DFAImpl i0 qs fs tr) =
        D.vsep [ D.text "State(s):" D.<+> D.text (show qs),
                 D.text "Initial: " D.<+> D.text (show i0),
                 D.text "Final(s):" D.<+> D.text (show fs),
                 D.sep [D.text "Transition(s):", D.nest 2 (D.align (pprTrMap tr)) ] ]



-- toGrammar :: (GrammarD c g, Ord q) => DFAImpl c q -> g ()
-- toGrammar dfa = Defs.local $
--     letrS (statesDFAImpl dfa) $ \f -> do
--         return (makeProd f, f (initDFAImpl dfa))
--     where
--         -- makeProd :: GrammarD c g => (q -> g ()) -> q -> g ()
--         makeProd f q = do
--             asum [ emp A.<|> G.symbI cs *> f q' | (cs, q') <- fromMaybe [] $ M.lookup q (transDFAImpl dfa) ]
--             where
--                 emp = if isFinalDFAImpl dfa q then pure () else A.empty

--         letrS :: (Ord q, GrammarD c g) => S.Set q -> ((q -> g ()) -> DefM g (q -> g (), r)) -> DefM g r
--         letrS qs f | S.size qs == 1 =
--             let [q] = S.toList qs
--             in Defs.letr $ \a -> do
--                 (h, r) <- f $ \x -> if x == q then a else error "out of index"
--                 return (h q, r)
--         letrS qs f = letrSs (S.splitRoot qs) f

--         letrSs :: (Ord q, GrammarD c g) => [S.Set q] -> ((q -> g ()) -> DefM g (q -> g (), r)) -> DefM g r
--         letrSs [] f = snd <$> f (const $ error "out of index")
--         letrSs (qs:qss) f = letrS qs $ \fqs -> letrSs qss $ \fqss -> do
--             (h, r) <- f $ \x -> if x `S.member` qs then fqs x else fqss x
--             return (h, (h, r))

eliminateEps :: Ord q => NFA c q -> NFANE c q
eliminateEps (NFA (NFANE is fs tr) epsTr) = NFANE is fs' tr'
    where
        invEps i = fromMaybe [i] $ M.lookup i invEpsTr

        invEpsTr = epsClosure $ S.toList <$> M.fromListWith S.union [ (v, S.fromList [v, k]) | (k, vs) <- M.toList epsTr, v <- vs ]

        fs' = S.fromList [ q' | q <- S.toList fs, q' <- invEps q ]

        tr' = M.fromListWith (++) [ (i, v) | (k, v) <- M.toList tr, i <- invEps k ]



epsClosure :: Ord q => M.Map q [q] -> M.Map q [q]
epsClosure = go
    where
        go m = let (m', b) = runWriter $ extend m
               in if getAny b then go m' else m'

        -- not efficient
        extend :: Ord q => M.Map q [q] -> Writer Any (M.Map q [q])
        extend m = traverse (\ks ->
            let ks' = [ k' | k <- ks, k' <- fromMaybe [] $ M.lookup k m, k' `L.notElem` ks  ]
            in tell (Any $ not $ null ks') >> pure (ks ++ ks') ) m

-- renumberD :: Ord q => DFAImpl c q -> DFAImpl c Word
-- renumberD dfa@(DFAImpl _ states _ _) = mapStateMonotonicD q2i dfa
--     where
--         tbl = M.fromAscList $ zip (S.toList states) [0..fromIntegral (S.size states) - 1]
--         q2i q = fromJust $ M.lookup q tbl

renumberN :: Ord q => NFA c q -> NFA c Word
renumberN nfa@(NFA (NFANE is fs tr) etr) = mapStateMonotonicN q2i nfa
    where
        states = S.unions [is, fs, M.keysSet tr,
                           M.foldlWithKey' (\a k v -> S.insert k $ S.unions (a : map (S.singleton . snd) v) ) S.empty tr,
                           M.foldlWithKey' (\a k v -> S.insert k $ S.unions (a : map S.singleton v) ) S.empty etr ]
        tbl = M.fromAscList $ zip (S.toList states) [0..fromIntegral (S.size states) -1]
        q2i q = fromJust $ M.lookup q tbl

mapStateD :: (Ord q, Ord q', Ord c, Enum c) => (q -> q') -> DFAImpl c q -> DFAImpl c q'
mapStateD h (DFAImpl q0 states fs tr) = DFAImpl (h q0) (S.map h states) (S.map h fs) (M.fromList $ map (bimap h (canonizeDst . map (second h))) $ M.toList tr)

mapStateMonotonicD :: (Ord q, Ord q') => (q -> q') -> DFAImpl c q -> DFAImpl c q'
mapStateMonotonicD h (DFAImpl q0 states fs tr) =
    DFAImpl (h q0) (S.mapMonotonic h states) (S.mapMonotonic h fs) (M.fromAscList $ map (bimap h (map (second h))) $ M.toList tr)

-- mapStateN :: (Ord q, Ord q') => (q -> q') -> NFA c q -> NFA c q'
-- mapStateN h (NFA (NFANE is fs tr) etr) = NFA (NFANE (S.map h is) (S.map h fs) tr') etr'
--     where
--         tr'  = M.fromList $ map (bimap h (map (second h))) $ M.toList tr
--         etr' = M.fromList $ map (bimap h (map h)) $ M.toList etr

mapStateMonotonicN :: (Ord q, Ord q') => (q -> q') -> NFA c q -> NFA c q'
mapStateMonotonicN h (NFA (NFANE is fs tr) etr) = NFA (NFANE (S.mapMonotonic h is) (S.mapMonotonic h fs) tr') etr'
    where
        tr'  = M.fromAscList $ map (bimap h (map (second h))) $ M.toList tr
        etr' = M.fromAscList $ map (bimap h (map h)) $ M.toList etr

type GroupID = Word

reduceImpl :: forall q c. (Ord q) => DFAImpl c q -> DFAImpl c q
reduceImpl (DFAImpl i qs fs tr) =
    DFAImpl i reachable (S.intersection reachable fs) (tr `M.restrictKeys` reachable)
    where
        reachable =
            let (g, v2i, k2v) = Graph.graphFromEdges [ (k, k, ks) | k <- S.toList qs, let ks = maybe [] (map snd) $ M.lookup k tr ]
            in case k2v i of
                Nothing -> S.empty
                Just v0 -> S.fromList $ map (fst3 . v2i) $ Graph.reachable g v0
            where
                fst3 (a, _, _) = a

minimizeImpl :: forall q c. (Ord q, Ord c, Enum c) => DFAImpl c q -> DFAImpl c GroupID
minimizeImpl dfa =
    let part0 = M.fromAscList $ map (\q -> (q, if q `S.member` finalsDFAImpl dfa then 0 else 1)) allStates
        partF = go part0
        q2i q = fromJust $ M.lookup q partF
    in reduceImpl $ mapStateD q2i dfa
    where
        allStates :: [q]
        allStates = S.toList (statesDFAImpl dfa)

        groupID :: M.Map q GroupID -> q -> GroupID
        groupID part q = fromJust $ M.lookup q part

        footprint :: M.Map q GroupID -> q -> [(RSet c, GroupID)]
        footprint part q = canonizeDst $ maybe [] (map (second $ groupID part)) $ M.lookup q (transDFAImpl dfa)


        -- regroups states by footprint
        refine :: M.Map q GroupID -> M.Map q GroupID
        refine part =
            let mp = M.fromListWith (++) [ ((groupID part q, footprint part q), [q]) | q <- allStates ]
            in M.fromList [ (q, ix) | (qs, ix) <- zip (M.elems mp) [0..], q <- qs ]

        go part =
            let part' = refine part
            in if maximum part < maximum part' then go part' else part'

canonizeDst :: (Ord c, Enum c, Ord q) => [(RSet c, q)] -> [(RSet c, q)]
canonizeDst = L.sortBy (compare `on` (RS.findMin . fst)) . map swap . M.toList . M.fromListWith RS.union . map swap
    where
        swap (a, b) = (b, a)

determinizeImpl :: forall c q. (Ord c, Enum c, Ord q) => NFANE c q -> DFAImpl c (S.Set q)
determinizeImpl (NFANE is fs tr) = go [is] S.empty M.empty
    where
        go :: [ S.Set q ] -> S.Set (S.Set q) -> M.Map (S.Set q) [(RSet c, S.Set q)] -> DFAImpl c (S.Set q)
        go [] visited trans = DFAImpl is visited (S.filter (any (`S.member` fs)) visited) trans
        go (qs:qss) visited trans
            | qs `S.member` visited = go qss visited trans
            | otherwise =
                let dests = makeNewTrans qs
                in go (map snd dests ++ qss) (S.insert qs visited) (M.insert qs dests trans)

        makeNewTrans :: S.Set q -> [(RSet c, S.Set q)]
        makeNewTrans = goT . concatMap (\q -> fromMaybe [] $ M.lookup q tr) . S.toList
            where
                goT :: [(RSet c, q)] -> [(RSet c, S.Set q)]
                goT []           = []
                goT ((c,q):rest) = insert c (S.singleton q) (goT rest)

                insert :: RSet c -> S.Set q -> [(RSet c, S.Set q)] -> [(RSet c, S.Set q)]
                insert cs qs [] = [(cs, qs)]
                insert cs qs ((cs',qs'):rest)
                    | RS.null cs       = (cs',qs'):rest
                    | RS.null csCommon = (cs',qs'):insert cs qs rest
                    | otherwise        = (cs1, qs):(csCommon, S.union qs qs'):(cs2, qs'):insert cs1 qs rest
                    where
                        csCommon = RS.intersection cs cs'
                        cs1      = RS.difference cs  cs'
                        cs2      = RS.difference cs' cs

complete :: (Bounded c, Enum c, Ord c) => DFAImpl c Word  -> DFAImpl c Word
complete a =
    let DFAImpl i qs fs tr = mapStateMonotonicD (+1) a
    in DFAImpl i (S.insert 0 qs) fs (fmap completeTr (foldr (\k -> M.insertWith (++) k []) tr qs)`M.union` dtr)
    where
        completeTr :: (Bounded c, Enum c, Ord c) => [(RSet c, Word )] -> [(RSet c, Word )]
        completeTr dst =
            let dom = L.foldl' (\r (cs,_) -> RS.union r cs) RS.empty dst
            in if RS.isFull dom then dst
               else                  (RS.complement dom, 0):dst
        dtr :: Bounded  c=> M.Map Word  [(RSet c, Word )]
        dtr = M.singleton 0 [(RS.full, 0)]


intersectTrans :: (Ord p, Ord q, Ord c) => M.Map p [(RSet c, p)] -> M.Map q [(RSet c, q)] -> M.Map (p, q) [(RSet c, (p,q))]
intersectTrans tr1 tr2 =
    -- (\a -> trace (show $ D.vsep [D.text "tr1:" D.<+> D.align (pprTrMap tr1), D.text "tr2:" D.<+> D.align (pprTrMap tr2), D.text "res:" D.<+> D.align (pprTrMap a)]) a) $
    M.fromListWith (++) [ ( (k1, k2), makeEntries k1 k2) | k1 <- M.keys tr1, k2 <- M.keys tr2 ]
    where
        makeEntries k1 k2 =
            filter (not . RS.null . fst) $
            [ (RS.intersection cs1 cs2, (q1, q2))
             | (cs1, q1) <- fromMaybe [] $ M.lookup k1 tr1,
               (cs2, q2) <- fromMaybe [] $ M.lookup k2 tr2 ]

toDFA :: (Ord c, Enum c, Ord q) => NFA c q -> DFA c
toDFA = minimizeImpl . determinizeImpl . eliminateEps

toNFA :: DFA c -> NFA c Word
toNFA (DFAImpl i _ fs tr) = NFA (NFANE (S.singleton i) fs tr) M.empty

-- singleton :: (Ord c, Bounded c, Enum c) => c -> DFA c
-- singleton c = DFAImpl 0 (S.fromList [0,1,2]) (S.singleton 1)
--                 (M.fromList [(0, [ (setC, 1), (nonC, 2) ]), (1, [ (RS.full, 2) ]), (2, [ (RS.full, 2) ]) ])
--     where
--         setC = RS.singleton c
--         nonC = RS.complement setC


instance IsString (NFA Char Word ) where
    fromString = mconcat . map singleton

instance IsString (DFA Char) where
    fromString = mconcat . map singleton


class Monoid r => Regex c r | r -> c where
    empty :: r
    empty = complement full


    full  :: r
    full = complement empty

    union :: r -> r -> r
    union r1 r2 = complement (complement r1 `intersection` complement r2)

    intersection :: r -> r -> r
    intersection r1 r2 = complement (complement r1 `union` complement r2)

    singleton :: c -> r
    singleton = fromRSet . RS.singleton
    {-# INLINE singleton #-}

    fromRSet :: RSet c -> r

    star :: r -> r

    complement :: r -> r
    complement r = full `difference` r

    difference :: r -> r -> r
    difference r1 r2 = r1 `intersection` complement r2

range :: (Regex c r, Ord c) => c -> c -> r
range c1 c2 = fromRSet $ RS.singletonRange (c1, c2)

plus :: (Regex c r) => r -> r
plus r = r <> star r

unions :: Regex c r => [r] -> r
unions = foldr union empty

intersections :: Regex c r => [r] -> r
intersections = foldr intersection full

emptyNFA :: Bounded c => NFA c Word
emptyNFA = NFA (NFANE S.empty S.empty M.empty) M.empty

fullNFA :: Bounded c => NFA c Word
fullNFA = NFA (NFANE (S.singleton 0) (S.singleton 0) (M.fromList [(0, [(RS.full, 0)])])) M.empty

unionNFA :: NFA c Word  -> NFA c Word  -> NFA c Word
unionNFA a1 a2 =
    let NFA (NFANE is1 fs1 tr1) etr1 = mapStateMonotonicN ((+ 1) . (2 *)) a1
        NFA (NFANE is2 fs2 tr2) etr2 = mapStateMonotonicN (2 *) a2
    in NFA (NFANE (S.union is1 is2) (S.union fs1 fs2) (M.unionWith (++) tr1 tr2)) (M.unionWith (++) etr1 etr2)



intersectionNFA :: Ord c => NFA c Word  -> NFA c Word  -> NFA c Word
intersectionNFA a1 a2 =
    let NFANE is1 fs1 tr1 = eliminateEps a1
        NFANE is2 fs2 tr2 = eliminateEps a2
        is = S.cartesianProduct is1 is2
        fs = S.cartesianProduct fs1 fs2
        tr = intersectTrans tr1 tr2
    in renumberN $ NFA (NFANE is fs tr) M.empty


starNFA :: NFA c Word  -> NFA c Word
starNFA a =
    let (NFA (NFANE is fs tr) etr) = mapStateMonotonicN (+1) a
        etr' = M.fromList $ (0, S.toList is) : [ (f, [0]) | f <- S.toList fs ]
    in NFA (NFANE (S.singleton 0) (S.singleton 0) tr) (M.unionWith (++) etr etr')

complementNFA :: (Enum c, Bounded c, Ord c) => NFA c Word  -> NFA c Word
complementNFA a =
    let DFAImpl i qs fs tr = complete $ minimizeImpl $ determinizeImpl $ eliminateEps a
    in NFA (NFANE (S.singleton i) (S.difference qs fs) tr) M.empty

appendNFA :: NFA c Word  -> NFA c Word  -> NFA c Word
appendNFA a1 a2 =
    let NFA (NFANE is1 fs1 tr1) etr1 = mapStateMonotonicN ((+ 1) . (2 *)) a1
        NFA (NFANE is2 fs2 tr2) etr2 = mapStateMonotonicN (2 *) a2
        etr' = M.fromList [ (f, S.toList is2) | f <- S.toList fs1 ]
    in NFA (NFANE is1 fs2 (M.unionWith (++) tr1 tr2)) (M.unionsWith (++) [etr1, etr2, etr' ])

instance Semigroup (NFA c Word ) where
    (<>) = appendNFA

instance Monoid (NFA c Word ) where
    mempty = NFA (NFANE (S.singleton 0) (S.singleton 0) M.empty) M.empty

instance (Bounded c, Enum c, Ord c) => Regex c (NFA c Word ) where
    empty = emptyNFA
    {-# INLINE empty #-}
    full  = fullNFA
    {-# INLINE full #-}

    union = unionNFA
    {-# INLINE union #-}

    intersection = intersectionNFA
    {-# INLINE intersection #-}

    fromRSet cs = NFA (NFANE (S.singleton 0) (S.singleton 1) (M.fromList [(0, [(cs, 1)])])) M.empty
    {-# INLINE fromRSet #-}

    star = starNFA
    {-# INLINE star #-}

    complement = complementNFA
    {-# INLINE complement #-}

instance (Enum c, Ord c) => Semigroup (DFA c) where
    a1 <> a2 = toDFA (toNFA a1 <> toNFA a2)

instance (Enum c, Ord c) => Monoid (DFA c) where
    mempty = DFAImpl 0 (S.singleton 0) (S.singleton 0) M.empty

instance (Bounded c, Enum c, Ord c) => Regex c (DFA c) where
    empty = DFAImpl 0 (S.singleton 0) S.empty M.empty
    full  = DFAImpl 0 (S.fromAscList [0,1]) (S.singleton 1) (M.fromAscList [(0, [ (RS.full, 1) ]), (1, [ (RS.full, 1) ])])

--    union (mapStateMonotonicD (2 *) . complete -> DFAImpl i qs fs tr) (mapStateMonotonicD ((+ 1) . (2 *)).  complete -> DFAImpl i' qs' fs' tr') =
    union a1 a2
       | DFAImpl i  qs  fs  tr  <- mapStateMonotonicD (2 *) $ complete a1,
         DFAImpl i' qs' fs' tr' <- mapStateMonotonicD ((+ 1) . (2 *)) $ complete a2 =
        minimizeImpl $ DFAImpl (i,i') (S.cartesianProduct qs qs') (S.fromList $ [ (q, f') | q <- S.toList qs, f' <- S.toList fs'] ++ [ (f, q') | f <- S.toList fs, q' <- S.toList qs']) (intersectTrans tr tr')

    intersection a1 a2
       | DFAImpl i  qs  fs  tr  <- mapStateMonotonicD (2 *) a1,
         DFAImpl i' qs' fs' tr' <- mapStateMonotonicD ((+ 1) . (2 *)) a2 =
        minimizeImpl $ DFAImpl (i,i') (S.cartesianProduct qs qs') (S.cartesianProduct fs fs') (intersectTrans tr tr')

    fromRSet cs = DFAImpl 0 (S.fromAscList [0, 1]) (S.singleton 1) (M.singleton 0 [ (cs, 1) ])

    star r = toDFA (star (toNFA r))

    complement a =
        let DFAImpl i qs fs tr = complete a
        in DFAImpl i qs (S.difference qs fs) tr



-- >>> D.ppr $ (star (singleton 'a' <> singleton 'b') :: DFA Char)
-- Initial:  0
-- Final(s): fromList [0]
-- Transition(s): 0 -> ['a'] 1; 1 -> ['b'] 0

-- >>> D.ppr $ (fromString "a" `union` fromString "b" :: DFA Char)
-- Initial:  2
-- Final(s): fromList [0]
-- Transition(s):
-- 0 -> ;
-- 2 -> ['\NUL'-'`''c'-'\1114111'] 4 | ['a'-'b'] 0;
-- 4 -> ['\NUL'-'\1114111'] 4

-- >>> D.ppr $ (star (fromRSet (RS.singletonRange ('a', 'z'))) :: DFA Char)
-- Initial:  0
-- Final(s): fromList [0]
-- Transition(s): 0 -> ['a'-'z'] 0
-- >>> D.ppr (complement (fromString "let") :: DFA Char)
-- Initial:  3
-- Final(s): fromList [0,2,3,4]
-- Transition(s):
-- 0 -> ['\NUL'-'\1114111'] 0;
-- 1 -> ;
-- 2 -> ['\NUL'-'d''f'-'\1114111'] 0 | ['e'] 4;
-- 3 -> ['\NUL'-'k''m'-'\1114111'] 0 | ['l'] 2;
-- 4 -> ['\NUL'-'s''u'-'\1114111'] 0 | ['t'] 1

-- >>> D.ppr $ (star (fromRSet (RS.singletonRange ('a', 'z'))) `intersection` complement (fromString "let") :: DFA Char)
-- Initial:  3
-- Final(s): fromList [0,2,3,4]
-- Transition(s):
-- 0 -> ['a'-'z'] 0;
-- 1 -> ;
-- 2 -> ['a'-'d''f'-'z'] 0 | ['e'] 4;
-- 3 -> ['a'-'k''m'-'z'] 0 | ['l'] 2;
-- 4 -> ['a'-'s''u'-'z'] 0 | ['t'] 1









