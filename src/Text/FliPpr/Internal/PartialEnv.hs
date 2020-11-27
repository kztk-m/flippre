{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- |
-- Partial environment. Unlike @Env@, this module is for non-recursive environment
-- of which entry can be missing.
module Text.FliPpr.Internal.PartialEnv where

import Control.Category
import Data.Kind
import Data.Typeable (Proxy, (:~:) (..))
import qualified Text.FliPpr.Doc as D
import Unsafe.Coerce

newtype VarT i env env' = VarT {runVarT :: forall a. Var i env a -> Var i env' a}

instance Category (VarT i) where
  id = VarT Prelude.id
  VarT f . VarT g = VarT (f Prelude.. g)

class PartialEnvImpl i where
  data Var i :: [Type] -> Type -> Type
  data Env i :: (Type -> Type) -> [Type] -> Type
  data Rep i :: [Type] -> Type

  lookupEnv :: Var i env a -> Env i t env -> Maybe (t a)
  updateEnv ::
    (forall a. t a -> t a -> Maybe (t a)) ->
    Var i env a ->
    t a ->
    Env i t env ->
    Maybe (Env i t env)

  mergeEnv ::
    (forall a. t a -> t a -> Maybe (t a)) ->
    Env i t env ->
    Env i t env ->
    Maybe (Env i t env)

  emptyEnv :: Env i t '[]
  undeterminedEnv :: Rep i env -> Env i t env

  extendEnv ::
    Env i t env ->
    Maybe (t a) ->
    (Env i t (a : env), Var i (a : env) a, VarT i env (a : env))

  emptyRep :: Rep i '[]
  isEmptyRep :: Rep i r -> Maybe (r :~: '[])

  extendRep ::
    Rep i env ->
    Proxy a ->
    (Rep i (a : env), Var i (a : env) a, VarT i env (a : env))

  popEnv :: Env i t (a : env) -> (Maybe (t a), Env i t env)

  {-
    The following functions are meaningful only when
    env <= env'
  -}

  embedVar :: Rep i env -> Rep i env' -> Var i env a -> Var i env' a
  embedEnv :: Rep i env -> Rep i env' -> Env i t env -> Env i t env'

  -- for debugging
  toIndex :: Var i env a -> Int
  pprEnv :: Env i t env' -> D.Doc

data U

data Untype = forall a. Untype a

instance Show Untype where
  show _ = "<abstract>"

unsafeCast :: Untype -> a
unsafeCast (Untype a) = unsafeCoerce a

data EnvImpl
  = EEmp
  | EUndet
  | EExt (Maybe Untype) EnvImpl
  deriving (Show)

instance PartialEnvImpl U where
  newtype Var U _env _a = VarU Int
  newtype Env U _t _a = EnvU EnvImpl deriving (Show)

  newtype Rep U _env = RepU Int deriving (Show)

  lookupEnv (VarU i) (EnvU es) = unsafeCast <$> go i es
    where
      go :: Int -> EnvImpl -> Maybe Untype
      go 0 (EExt v _) = v
      go n (EExt _ e) = go (n -1) e
      go _ _ = Nothing

  updateEnv mg (VarU i) v (EnvU es) = EnvU <$> go i v es
    where
      go 0 v (EExt Nothing e) = Just (EExt (Just (Untype v)) e)
      go 0 v (EExt (Just v') e)
        | Just r <- mg v (unsafeCast v') = Just (EExt (Just (Untype r)) e)
      go 0 v EUndet = Just $ EExt (Just (Untype v)) EUndet
      go n v (EExt v' e) = EExt v' <$> go (n -1) v e
      go n v EUndet = EExt Nothing <$> go (n -1) v EUndet
      go _ _ _ = Nothing

  mergeEnv mg (EnvU es) (EnvU es') = EnvU <$> go es es'
    where
      go EEmp EEmp = return EEmp
      go e EUndet = return e
      go EUndet e = return e
      go (EExt Nothing e) (EExt v' e') =
        EExt v' <$> go e e'
      go (EExt v e) (EExt Nothing e') =
        EExt v <$> go e e'
      go (EExt (Just v) e) (EExt (Just v') e') = do
        e'' <- go e e'
        v'' <- mg (unsafeCast v) (unsafeCast v')
        return $ EExt (Just (Untype v'')) e''
      go _ _ = Nothing

  emptyEnv = EnvU EEmp
  undeterminedEnv _ = EnvU EUndet

  extendEnv (EnvU env) v =
    ( EnvU (EExt (Untype <$> v) env),
      VarU 0,
      VarT (\(VarU i) -> VarU (i + 1))
    )

  emptyRep = RepU 0
  isEmptyRep (RepU k) =
    if k == 0
      then Just (unsafeCoerce Refl)
      else Nothing

  extendRep (RepU k) _ =
    (RepU (k + 1), VarU 0, VarT (\(VarU i) -> VarU (i + 1)))

  popEnv (EnvU env) =
    let (v, e) = go env
     in (unsafeCast <$> v, EnvU e)
    where
      go (EExt v e) = (v, e)
      go EUndet = (Nothing, EUndet)
      go EEmp = error "Cannot happen"

  embedVar (RepU k) (RepU k') (VarU i) = VarU (i + (k' - k))
  embedEnv (RepU k) (RepU k') (EnvU env) = EnvU (go (k' - k) env)
    where
      go 0 env = env
      go n env = EExt Nothing (go (n -1) env)

  toIndex (VarU i) = i
  pprEnv (EnvU impl) = D.group $ D.text "<" D.<> go (0 :: Int) impl D.<> D.text ">"
    where
      go _ EEmp = D.empty
      go _ EUndet = D.text "???"
      go n (EExt b r) =
        (D.ppr n D.<> D.text ":" D.<> maybe (D.text "_") (const $ D.text "*") b) D.</> go (n + 1) r

data UB

data BEnv = BEnd | BSkip Int BEnv | BExt Untype BEnv
  deriving (Show)

bskip :: Int -> BEnv -> BEnv
bskip 0 e = e
bskip n (BSkip m e) = BSkip (n + m) e
bskip n e = BSkip n e

bskip' :: Int -> BEnv -> BEnv
bskip' 0 e = e
bskip' n e = BSkip n e

instance PartialEnvImpl UB where
  newtype Var UB _env _a = VarUB Int
  newtype Env UB _t _a = EnvUB BEnv deriving (Show)

  newtype Rep UB _env = RepUB Int deriving (Show)

  lookupEnv (VarUB i) (EnvUB es) = unsafeCast <$> go i es
    where
      go :: Int -> BEnv -> Maybe Untype
      go 0 (BExt v _) = Just v
      go n (BExt _ r) = go (n -1) r
      go _ BEnd = Nothing
      go n (BSkip m e) =
        let kk = min n m
         in go (n - kk) (bskip' (m - kk) e)

  updateEnv mg (VarUB i) v (EnvUB es) = EnvUB <$> go i v es
    where
      go 0 v (BExt u e) | Just r <- mg v (unsafeCast u) = pure $ BExt (Untype r) e
      go 0 v (BSkip m e) = pure $ BExt (Untype v) (bskip' (m -1) e)
      go n v (BExt u e) = BExt u <$> go (n -1) v e
      go n v (BSkip m e) =
        let kk = min n m
         in bskip kk <$> go (n - kk) v (bskip' (m - kk) e)
      go _ _ _ = Nothing

  mergeEnv mg (EnvUB es) (EnvUB es') = EnvUB <$> go es es'
    where
      go (BExt v1 e1) (BExt v2 e2) = do
        e <- go e1 e2
        r <- mg (unsafeCast v1) (unsafeCast v2)
        return (BExt (Untype r) e)
      go (BExt v1 e1) (BSkip n e2) = do
        e <- go e1 (if n == 1 then e2 else bskip' (n -1) e2)
        return (BExt v1 e)
      go (BSkip n e1) (BExt v2 e2) = do
        e <- go (if n == 1 then e1 else bskip' (n -1) e1) e2
        return (BExt v2 e)
      go (BSkip n1 e1) (BSkip n2 e2) = do
        let m = min n1 n2
        e <- go (bskip' (n1 - m) e1) (bskip' (n2 - m) e2)
        return (BSkip m e)
      go BEnd BEnd = Just BEnd
      go _ _ = Nothing -- unreachable

  emptyEnv = EnvUB BEnd
  undeterminedEnv (RepUB n) = EnvUB (BSkip n BEnd)

  extendEnv (EnvUB env) v =
    let newenv = case v of
          Just val -> EnvUB (BExt (Untype val) env)
          Nothing -> EnvUB (bskip 1 env)
     in (newenv, VarUB 0, VarT (\(VarUB i) -> VarUB (i + 1)))

  emptyRep = RepUB 0
  isEmptyRep (RepUB k) =
    if k == 0
      then Just (unsafeCoerce Refl)
      else Nothing

  extendRep (RepUB k) _ =
    (RepUB (k + 1), VarUB 0, VarT (\(VarUB i) -> VarUB (i + 1)))

  popEnv (EnvUB env) =
    let (v, e) = go env
     in (unsafeCast <$> v, EnvUB e)
    where
      go (BExt v e) = (Just v, e)
      go (BSkip n e) = (Nothing, bskip' (n -1) e)
      go BEnd = error "Cannot happen"

  embedVar (RepUB k) (RepUB k') (VarUB i) = VarUB (i + (k' - k))
  embedEnv (RepUB k) (RepUB k') (EnvUB env) = EnvUB $ bskip (k' - k) env

  toIndex (VarUB i) = i
  pprEnv (EnvUB impl) = D.group $ D.text "<" D.<> go (0 :: Int) impl D.<> D.text ">"
    where
      go _ BEnd = D.empty
      go n (BSkip m e) = D.text "_" D.<> D.brackets (D.text (show m)) D.</> go (n + m) e
      go n (BExt _ r) =
        (D.ppr n D.<> D.text ":" D.<> D.text "*") D.</> go (n + 1) r
