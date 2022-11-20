{-# Language TypeSynonymInstances, FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, UndecidableInstances, DeriveDataTypeable,
             TypeFamilies, TupleSections, BangPatterns, TemplateHaskell, QuasiQuotes #-}


module Main where

import Control.Exception.Safe
import Control.Monad.Except
import Control.Monad.Trans.State.Strict
import Control.Egison hiding (Pattern)
import qualified Control.Egison as Egison

main :: IO ()
main = do
  let topExprs = [idDef, compDef, natDef, zeroDef, oneDef, eqDef, reflDef, iReflDef, plusDef, congDef, plusZeroDef, axiomKDef, lteDef, antisymDef]
  Right topExprs' <- runCheckM (mapM desugarTopExpr topExprs)
  let envV = initTopVEnv topExprs'
  let envT = initTopTEnv topExprs'
  let envD = initTopDEnv topExprs'
  let envC = initTopCEnv topExprs'
  let env = (envV, envT, envD, envC)
  mapM_ (\(e, e') -> do
           putStrLn ("input: " ++ show e)
           ret <- runCheckM (checkTopExpr env e')
           case ret of
             Left err -> print err
             Right expr -> putStrLn ("output: " ++ show expr))
    (zip topExprs topExprs')
  
--- Monad

data PwlError
  = Default String
  | TypeDoesNotMatch Expr Expr
  | UnboundVariable Name
  | ShouldBe String Expr
  | NotConvertible Expr Expr

instance Show PwlError where
  show (Default msg) = "Type error: " ++ msg
  show (TypeDoesNotMatch v t) = "Type error: the type of " ++ show v ++ " does not match " ++ show t ++ "."
  show (UnboundVariable n) = "Type error: " ++ n ++ " is unbound."
  show (ShouldBe s v) = "Type error: " ++ show v ++ " should be " ++ s ++ "."
  show (NotConvertible e1 e2) = "Type error: " ++ show e1 ++ " and " ++ show e2 ++ " are not convertible."

instance Exception PwlError

data RState = RState
  { indexCounter :: Int
  }

initialRState :: RState
initialRState = RState
  { indexCounter = 0
  }

type RuntimeT m = StateT RState m

type RuntimeM = RuntimeT IO

class (Applicative m, Monad m) => MonadRuntime m where
  fresh :: m String
  addFresh :: String -> m String

instance Monad m => MonadRuntime (RuntimeT m) where
  fresh = do
    st <- get
    modify (\st -> st { indexCounter = indexCounter st + 1 })
    return $ "$_" ++ show (indexCounter st)
  addFresh name@('$' : _) = do
    st <- get
    modify (\st -> st { indexCounter = indexCounter st + 1 })
    return $ name ++ "_" ++ show (indexCounter st)
  addFresh name = do
    st <- get
    modify (\st -> st { indexCounter = indexCounter st + 1 })
    return $ "$" ++ name ++ "_" ++ show (indexCounter st)

runRuntimeT :: Monad m => RuntimeT m a -> m (a, RState)
runRuntimeT = flip runStateT initialRState

evalRuntimeT :: Monad m => RuntimeT m a -> m a
evalRuntimeT = flip evalStateT initialRState

type CheckM = ExceptT PwlError RuntimeM

runCheckM :: CheckM a -> IO (Either PwlError a)
runCheckM ma = do
  (ret, _) <- runRuntimeT (runExceptT ma)
  return ret

instance MonadRuntime CheckM where
  fresh = lift fresh
  addFresh s = lift (addFresh s)
  
--- Datatypes

type Name = String

data TopExpr
  = DataDecE Name [(Name, Expr)] [(Name, Expr)] [(Name, [(Name, Expr)], Expr)] -- datatype name, telescope, indices, [(constructor name, args, type)]
  | DefE Name Expr Expr -- name, type, expr
  | DefFunE Name [(Name, Expr)] Expr Expr -- SHOULD DESUGARED: name, types of arguments, type of return value, expr
  | DefCaseE Name [(Name, Expr)] Expr [([Pattern], Expr)] -- SHOULD DESUGARED: name, types of arguments, type of return value, [(patterns, body)]
 deriving Show

data Expr
  = VarE Name
  | ArrowE Expr Expr -- SHOULD DESUGARED
  | PiE Name Expr Expr
  | LambdaE Name Expr
  | LambdaMultiE [Name] Expr -- SHOULD DESUGARED
  | ApplyE Expr Expr
  | ApplyMultiE Expr [Expr] -- SHOULD DESUGARED
  | SigmaE Name Expr Expr
  | PairE Expr Expr
  | Proj1E Expr
  | Proj2E Expr
  | UniverseE Integer
  | UniverseAlphaE -- Only internal use: Universe for some integer alpha
  | UnitTypeE
  | UnitE
  | TypeE Name [Expr] [Expr]
  | DataE Name [Expr]
  | CaseE [(Expr, TVal)] [([Pattern], Expr)]
 deriving (Show, Eq)

data Pattern
  = Wildcard
  | PatVar Name
  | DataPat Name [Pattern]
  | ValuePat Expr
 deriving (Show, Eq)

data PatternM = PatternM
instance Matcher PatternM Pattern

dataPat :: Egison.Pattern (PP Name, PP [Pattern]) PatternM Pattern (Name, [Pattern])
dataPat _ _ (DataPat n ps) = pure (n, ps)

dataPatM :: m -> t -> (Something, List PatternM)
dataPatM _ _ = (Something, (List PatternM))

type TVal = Expr
type Val = Expr

type Env = (VEnv, TEnv, DEnv, CEnv)
type VEnv = [(Name, Expr)] -- Value environment
type TEnv = [(Name, TVal)] -- Type environment
type DEnv = [(Name, (Telescope, Indices))] -- Datatype enviroment
type CEnv = [(Name, (Telescope, Telescope, TVal))] -- Constructor enviroment
  
type Context = [(Name, TVal)]
type Telescope = [(Name, TVal)]
type Indices = [(Name, TVal)]

initTopVEnv :: [TopExpr] -> VEnv
initTopVEnv [] = []
initTopVEnv (DefE n _ e : rs) = (n, e) : (initTopVEnv rs)
initTopVEnv (_ : rs) = initTopVEnv rs

initTopTEnv :: [TopExpr] -> TEnv
initTopTEnv [] = []
initTopTEnv (DefE n t _ : rs) = (n, t) : (initTopTEnv rs)
initTopTEnv (_ : rs) = initTopTEnv rs

initTopDEnv :: [TopExpr] -> DEnv
initTopDEnv [] = []
initTopDEnv (DataDecE n ts is _ : rs) = (n, (ts, is)) : (initTopDEnv rs)
initTopDEnv (_ : rs) = initTopDEnv rs

initTopCEnv :: [TopExpr] -> CEnv
initTopCEnv [] = []
initTopCEnv (DataDecE _ ts _ cs : rs) = (map f cs) ++ (initTopCEnv rs)
 where
  f (c, as, t) = (c, (ts, as, t))
initTopCEnv (_ : rs) = initTopCEnv rs

getFromEnv :: [(Name, a)] -> Name -> CheckM a
getFromEnv env x =
  case getFromEnv' env x of
    Nothing -> throwError (UnboundVariable x)
    Just t  -> return t

getFromEnv' :: [(Name, a)] -> Name -> Maybe a
getFromEnv' env x =
  match dfs env (List (Pair Eql Something))
    [[mc| _ ++ (#x, $t) : _ -> Just t |],
     [mc| _ -> Nothing |]]

getFromVEnv :: Env -> Name -> CheckM (Maybe Expr)
getFromVEnv (venv, _, _, _) x = return (getFromEnv' venv x) -- TODO: alpha conversion
     
getFromTEnv :: Env -> Name -> CheckM TVal
getFromTEnv (_, tenv, _, _) x = getFromEnv tenv x
     
getFromDEnv :: Env -> Name -> CheckM (Telescope, Indices)
getFromDEnv (_, _, denv, _) x = do
  (ts, is) <- getFromEnv denv x
  tns <- mapM addFresh (map fst ts)
  ins <- mapM addFresh (map fst is)
  let tms = map (\(s, s') -> (s, VarE s')) (zip (map fst ts) tns)
  let ims = map (\(s, s') -> (s, VarE s')) (zip (map fst is) ins)
  return (zip tns (map (substitute tms) (map snd ts)), zip ins (map (substitute (tms ++ ims)) (map snd is)))
     
getFromCEnv :: Env -> Name -> CheckM (Telescope, Telescope, TVal)
getFromCEnv (_, _, _, cenv) x = do
  (ts, as, b) <- getFromEnv cenv x
  tns <- mapM addFresh (map fst ts)
  ans <- mapM addFresh (map fst as)
  let tms = map (\(s, s') -> (s, VarE s')) (zip (map fst ts) tns)
  let ams = map (\(s, s') -> (s, VarE s')) (zip (map fst as) ans)
  return (zip tns (map (substitute tms) (map snd ts)), zip ans (map (substitute (tms ++ ams)) (map snd as)), substitute (tms ++ ams) b)

addToVEnv1 :: Env -> Name -> TVal -> Env
addToVEnv1 (venv, tenv, denv, cenv) x a = (venv ++ [(x, a)], tenv, denv, cenv)
                             
addToVEnv :: Env -> Context -> Env
addToVEnv (venv, tenv, denv, cenv) cs = (venv ++ cs, tenv, denv, cenv)
                             
addToTEnv1 :: Env -> Name -> TVal -> Env
addToTEnv1 (venv, tenv, denv, cenv) x a = (venv, tenv ++ [(x, a)], denv, cenv)
                             
addToTEnv :: Env -> Context -> Env
addToTEnv (venv, tenv, denv, cenv) cs = (venv, tenv ++ cs, denv, cenv)
                             
--- Desugar

desugarTopExpr :: TopExpr -> CheckM TopExpr
desugarTopExpr (DataDecE n as is cs) = do
  as' <- mapM (\(s, e) -> (,) <$> replaceWc s <*> desugarExpr e) as
  is' <- mapM (\(s, e) -> (,) <$> replaceWc s <*> desugarExpr e) is
  cs' <- mapM (\(s, ts, e) -> do
                  s' <- replaceWc s
                  ts' <- mapM (\(s, e) -> (,) <$> replaceWc s <*> desugarExpr e) ts
                  e' <- desugarExpr e
                  return (s, ts', e')) cs
  return (DataDecE n as' is' cs')
desugarTopExpr (DefE n t (LambdaMultiE as e)) = do
  t' <- desugarExpr t
  e' <- desugarExpr e
  return (DefE n t' (LambdaMultiE as e'))
desugarTopExpr (DefE n t e) = do
  t' <- desugarExpr t
  e' <- desugarExpr e
  return (DefE n t' e')
desugarTopExpr (DefFunE n as t e) = do
  let t' = foldr (\(s, u) t' -> PiE s u t') t as
  let e' = LambdaMultiE (map fst as) e
  desugarTopExpr (DefE n t' e')
desugarTopExpr (DefCaseE n as t cs) = do
  as'  <- mapM (\(s, e) -> (,) <$> replaceWc s <*> desugarExpr e) as
  desugarTopExpr (DefFunE n as' t (CaseE (map (\(s, e) -> (VarE s, e)) as') cs))
  
desugarExpr :: Expr -> CheckM Expr
desugarExpr (ArrowE t1 t2) = do
  s <- fresh
  desugarExpr (PiE s t1 t2)
desugarExpr (PiE s t1 t2) = PiE <$> replaceWc s <*> desugarExpr t1 <*> desugarExpr t2
desugarExpr (LambdaMultiE ns e) = desugarExpr (foldr (\n e' -> LambdaE n e') e ns)
desugarExpr (ApplyMultiE (VarE s) as) = ApplyMultiE (VarE s) <$> mapM desugarExpr as
desugarExpr (ApplyMultiE f as) = desugarExpr (foldl (\f' a -> ApplyE f' a) f as)
desugarExpr (LambdaE n e1) = LambdaE n <$> (desugarExpr e1)
desugarExpr (ApplyE e1 e2) = ApplyE <$> (desugarExpr e1) <*> (desugarExpr e2)
desugarExpr (SigmaE n e1 e2) = SigmaE n <$> (desugarExpr e1) <*> (desugarExpr e2)
desugarExpr (PairE e1 e2) = PairE <$> (desugarExpr e1) <*> (desugarExpr e2)
desugarExpr (Proj1E e1) = Proj1E <$> (desugarExpr e1)
desugarExpr (Proj2E e1) = Proj2E <$> (desugarExpr e1)
desugarExpr (CaseE ts cs) = CaseE <$> (mapM (\(s, e) -> (,) <$> desugarExpr s <*> desugarExpr e) ts) <*> (mapM (\(ps, e) -> (,) <$> (mapM desugarPattern ps) <*> (desugarExpr e)) cs)
desugarExpr (TypeE c ts is) = TypeE c <$> mapM desugarExpr ts <*> mapM desugarExpr is
desugarExpr (DataE c es) = DataE c <$> mapM desugarExpr es
desugarExpr e = return e

desugarPattern :: Pattern -> CheckM Pattern
desugarPattern Wildcard = PatVar <$> fresh
desugarPattern (ValuePat e) = ValuePat <$> desugarExpr e
desugarPattern (DataPat n ps) = DataPat n <$> mapM desugarPattern ps
desugarPattern p = return p

replaceWc :: Name -> CheckM Name
replaceWc "_" = fresh
replaceWc s   = return s

--- Type checking

checkTopExpr :: Env -> TopExpr -> CheckM TopExpr
checkTopExpr env (DefE n t e) = do
  e' <- check env e t
  return (DefE n t e')
checkTopExpr _ e = return e

check :: Env -> Expr -> Expr -> CheckM Expr
check env (LambdaMultiE xs e) a = check env (foldr (\x e' -> LambdaE x e') e xs) a
check env (LambdaE x e) a = do
  a' <- evalWHNF env a
  case a' of
    PiE y b c | x == y -> do
      e' <- check (addToTEnv1 env x b) e c
      return (LambdaE x e')
    PiE y b c -> do
      x' <- addFresh x
      e' <- check (addToTEnv1 env x' b) (substitute1 x (VarE x') e) (substitute1 y (VarE x') c)
      return (LambdaE x' e')
    _ -> throwError (TypeDoesNotMatch (LambdaE x e) a')
check env e@(PairE e1 e2) a = do
  a' <- evalWHNF env a
  case a' of
    SigmaE x b c -> do
      s <- check env e1 b
      t <- check env e2 (substitute1 x s c)
      return (PairE s t)
    _ -> throwError (TypeDoesNotMatch e a')
check env e@(DataE c xs) a = do
  a' <- evalWHNF env a
  case a' of
    TypeE _ ts _ -> do
      (tts, xts, b) <- getFromCEnv env c
      (env', ts') <- checkTelescope env ts tts
      (env'', xs') <- checkTelescope env' xs xts
      isSubtype env'' (substitute ((zip (map fst tts) ts') ++ (zip (map fst xts) xs')) b) a'
      return (DataE c xs')
    _ -> throwError (TypeDoesNotMatch e a')
check env (CaseE ts mcs) a = do
  mcs' <- mapM (\(p, b) -> do
                   (p', tRet, vRet) <- checkPattern env ts p
                   b' <- check (addToTEnv env tRet) b (substitute vRet a)
                   return (p', b')
               ) mcs
  -- TODO: coverage check
  return (CaseE ts mcs')
check env e a = do
  (b, t) <- infer env e
  isSubtype env a b
  return t

checkTelescope :: Env -> [Expr] -> Telescope -> CheckM (Env, [Expr])
checkTelescope env [] [] = return (env, [])
checkTelescope env (x : xs) ((n, xt) : xts) = do
  x' <- check env x xt
  (env', xs') <- checkTelescope (addToTEnv1 env n xt) xs (map (\(n2, xt2) -> (n2, substitute1 n x' xt2)) xts)
  return (env', x' : xs')

infer :: Env -> Expr -> CheckM (Expr, Expr)
infer env e@(VarE x) = do
  a <- getFromTEnv env x
  return (a, e)
infer env (ApplyMultiE (VarE s) as) = do
  (a, e) <- infer env (foldl (\f' a -> ApplyE f' a) (VarE s) as)
  let e' = sugarToApplyMulti [] e
  return (a, e')
infer env (ApplyE e1 e2) = do
  (a, e1') <- infer env e1
  a' <- evalWHNF env a
  case a' of
    PiE x b c -> do
      e2' <- check env e2 b
      return (substitute1 x e2' c, ApplyE e1' e2')
    _ -> throwError (ShouldBe "function" e1)
infer env (Proj1E e) = do
  (a, t) <- infer env e
  a' <- evalWHNF env a
  case a' of
    SigmaE _ b _ -> do
      return (b, Proj1E t)
    _ -> throwError (ShouldBe "pair" e)
infer env (Proj2E e) = do
  (a, t) <- infer env e
  a' <- evalWHNF env a
  case a' of
    SigmaE x _ c -> do
      return (substitute1 x (Proj1E t) c, Proj2E t)
    _ -> throwError (ShouldBe "pair" e)
infer env (PiE x e1 e2) = do
  (c1, a) <- infer env e1
  (c2, b) <- infer (addToTEnv1 env x a) e2
  c1' <- evalWHNF env c1
  c2' <- evalWHNF env c2
  case (c1', c2') of
    (UniverseE i, UniverseE j) -> do
      return (UniverseE (max i j), PiE x a b)
    _ -> throwError (Default "infer Pi")
infer env (SigmaE x e1 e2) = do
  (c1, a) <- infer env e1
  (c2, b) <- infer (addToTEnv1 env x a) e2
  c1' <- evalWHNF env c1
  c2' <- evalWHNF env c2
  case (c1', c2') of
    (UniverseE i, UniverseE j) -> do
      return (UniverseE (max i j), SigmaE x a b)
    _ -> throwError (Default "infer Sigma")
infer _ e@UnitE = do
  return (UnitTypeE, e)
infer _ e@UnitTypeE = do
  return (UniverseE 0, e)
infer _ e@(UniverseE n) = do
  return (UniverseE (n + 1), e)
infer env e@(TypeE _ _ _) = do
  return (UniverseE 0, e)
infer _ e = throwError (Default ("infer not implemented:" ++ show e))

sugarToApplyMulti :: [Expr] -> Expr -> Expr
sugarToApplyMulti as (VarE s) = (ApplyMultiE (VarE s) as)
sugarToApplyMulti as (ApplyE f a) = sugarToApplyMulti (a : as) f

isSubtype :: Env -> Expr -> Expr -> CheckM ()
isSubtype env a b = do
  a' <- evalWHNF env a
  b' <- evalWHNF env b
  isSubtype' env a' b'

isSubtype' :: Env -> Expr -> Expr -> CheckM ()
isSubtype' _ (UniverseE i) (UniverseE j) | i + 1 == j = return ()
isSubtype' env (PiE x a1 b1) (PiE y a2 b2) =
  if x == y
    then do
      isConvertible env a1 a2 UniverseAlphaE
      isSubtype (addToTEnv1 env x a1) b1 b2
    else throwError (NotConvertible (PiE x a1 b1) (PiE y a2 b2))
isSubtype' env (SigmaE x a1 b1) (SigmaE y a2 b2) =
  if x == y
    then do
      isConvertible env a1 a2 UniverseAlphaE
      isSubtype (addToTEnv1 env x a1) b1 b2
    else throwError (NotConvertible (SigmaE x a1 b1) (SigmaE y a2 b2))
isSubtype' env a b = isConvertible' env a b UniverseAlphaE

areConvertible :: Env -> [Expr] -> [Expr] -> Telescope -> CheckM ()
areConvertible _ [] [] [] = return ()
areConvertible env (x:xs) (y:ys) ((n, xt):xts) = do
  isConvertible env x y xt
  areConvertible (addToTEnv1 env n x) xs ys (map (\(n2, a2) -> (n2, substitute1 n x a2)) xts)

isConvertible :: Env -> Expr -> Expr -> Expr -> CheckM ()
isConvertible env s t a = do
  s' <- evalWHNF env s
  t' <- evalWHNF env t
  a' <- evalWHNF env a
  isConvertible' env s' t' a'

isConvertible' :: Env -> Expr -> Expr -> Expr -> CheckM ()
isConvertible' env (UniverseE i) (UniverseE j) UniverseAlphaE =
  if i == j then return () else throwError (NotConvertible (UniverseE i) (UniverseE j))
isConvertible' env (PiE x a1 b1) (PiE y a2 b2) UniverseAlphaE =
  if x == y
    then do
      isConvertible env a1 a2 UniverseAlphaE
      isConvertible (addToTEnv1 env x a1) b1 b2 UniverseAlphaE
    else throwError (NotConvertible (PiE x a1 b1) (PiE y a2 b2))
isConvertible' env (SigmaE x a1 b1) (SigmaE y a2 b2) UniverseAlphaE =
  if x == y
    then do
      isConvertible env a1 a2 UniverseAlphaE
      isConvertible (addToTEnv1 env x a1) b1 b2 UniverseAlphaE
    else throwError (NotConvertible (SigmaE x a1 b1) (SigmaE y a2 b2))
isConvertible' env s t UnitTypeE = return ()
isConvertible' env s t (PiE x a b) = isConvertible (addToTEnv1 env x a) (ApplyE s (VarE x)) (ApplyE t (VarE x)) b
isConvertible' env s t (SigmaE x a b) = do
  isConvertible env (Proj1E s) (Proj1E t) a
  isConvertible env (Proj2E s) (Proj2E t) (substitute1 x (Proj1E s) b)
isConvertible' env (DataE n1 xs1) (DataE n2 xs2) (TypeE _ ts _) =
  if n1 == n2
    then do
      (tts, xts, _) <- getFromCEnv env n1
      areConvertible env xs1 xs2 (substituteWithTelescope tts ts xts)
    else throwError (NotConvertible (DataE n1 xs1) (DataE n2 xs2))
isConvertible' env (TypeE n1 ts1 is1) (TypeE n2 ts2 is2) UniverseAlphaE = -- Same body with the below
  if n1 == n2
    then do
      (tts, its) <- getFromDEnv env n1
      areConvertible env (ts1 ++ is1) (ts2 ++ is2) (tts ++ its)
    else throwError (NotConvertible (TypeE n1 ts1 is1) (TypeE n2 ts2 is2))
isConvertible' env (TypeE n1 ts1 is1) (TypeE n2 ts2 is2) (UniverseE _) = -- Same body with the above
  if n1 == n2
    then do
      (tts, its) <- getFromDEnv env n1
      areConvertible env (ts1 ++ is1) (ts2 ++ is2) (tts ++ its)
    else throwError (NotConvertible (TypeE n1 ts1 is1) (TypeE n2 ts2 is2))
isConvertible' env s t a = do
  if isNeutral s && isNeutral t
    then do
      _ <- isEqual env s t
      return ()
    else throwError (Default ("isConvertible' else: " ++ show (s, t)))

isEqual :: Env -> Expr -> Expr -> CheckM Expr
isEqual env (VarE x) (VarE y) =
  if x == y
    then do
      a <- getFromTEnv env x
      return a
    else throwError (Default ("isEqual var: " ++ show (x, y)))
isEqual env (ApplyMultiE s1 ts1) (ApplyMultiE s2 ts2) =
  isEqual env (foldl (\f' a -> ApplyE f' a) s1 ts1) (foldl (\f' a -> ApplyE f' a) s2 ts2)
isEqual env (ApplyE s1 t1) (ApplyE s2 t2) = do
  a <- isEqual env s1 s2
  a' <- evalWHNF env a
  case a' of
    PiE x b c -> do
      isConvertible env t1 t2 b
      return (substitute1 x t1 c)
    _ -> throwError (Default ("isEqual apply: " ++ show a'))
isEqual env (Proj1E s) (Proj1E t) = do
  a <- isEqual env s t
  a' <- evalWHNF env a
  case a' of
    SigmaE x b c -> do
      return b
    _ -> throwError (Default "isEqual proj1")
isEqual env (Proj2E s) (Proj2E t) = do
  a <- isEqual env s t
  a' <- evalWHNF env a
  case a' of
    SigmaE x b c -> do
      return (substitute1 x (Proj1E s) c)
    _ -> throwError (Default "isEqual proj2")
isEqual _ e1 e2 = throwError (Default ("isEqual not implemented:" ++ show (e1, e2)))

evalWHNF :: Env -> Expr -> CheckM Expr
evalWHNF env (VarE n) = do
  v <- getFromVEnv env n
  case v of
    Nothing -> return (VarE n)
    Just e  -> return e
evalWHNF env (ApplyMultiE e es) = do
  e' <- evalWHNF env e
  case e' of
    LambdaMultiE as b@(CaseE _ _) -> do
      ret <- evalWHNF env (substitute (zip as es) b)
      case ret of
        CaseE _ _ -> return (ApplyMultiE e es)
        _ -> return ret
    LambdaMultiE _ _ -> desugarExpr (ApplyMultiE e' es) >>= evalWHNF env
evalWHNF env (ApplyE e1 e2) = do
  e1' <- evalWHNF env e1
  case e1' of
    LambdaE x b -> return (substitute1 x e2 b)
    _ -> return (ApplyE e1' e2)
evalWHNF env (Proj1E e) = do
  e' <- evalWHNF env e
  case e' of
    PairE e1 _ -> evalWHNF env e1
    _ -> return e'
evalWHNF env (Proj2E e) = do
  e' <- evalWHNF env e
  case e' of
    PairE _ e2 -> evalWHNF env e2
    _ -> return e'
evalWHNF env (CaseE ts mcs) = do
  me <- evalMCs env ts mcs
  case me of
    Nothing -> return (CaseE ts mcs)
    Just e -> return e
evalWHNF _ e = return e

evalMCs :: Env -> [(Expr, TVal)] -> [([Pattern], Expr)] -> CheckM (Maybe Expr)
evalMCs _ ts [] = return Nothing
evalMCs env ts ((ps, b) : mcs) = do
  mret <- patternMatch env ps (map fst ts)
  case mret of
    Nothing -> evalMCs env ts mcs
    Just ret -> Just <$> evalWHNF env (substitute ret b)

patternMatch :: Env -> [Pattern] -> [Expr] -> CheckM (Maybe [(Name, Expr)])
patternMatch env ps ts = patternMatch' env []  ps ts

patternMatch' :: Env -> [(Name, Expr)] -> [Pattern] -> [Expr] -> CheckM (Maybe [(Name, Expr)])
patternMatch' _ ret [] [] = return (Just ret)
patternMatch' env ret (PatVar x : ps) (t : ts) = patternMatch' env (ret ++ [(x, t)]) ps ts
patternMatch' env ret (ValuePat v : ps) (t : ts) = do
  v' <- evalWHNF (addToVEnv env ret) v
  t' <- evalWHNF env t
  if v' == t'
    then  patternMatch' env ret ps ts
    else return Nothing
patternMatch' env ret (DataPat c qs : ps) (DataE c' us : ts) | c == c' = patternMatch' env ret (qs ++ ps) (us ++ ts)
patternMatch' _ _ _ _ = return Nothing

isNeutral :: Expr -> Bool
isNeutral (VarE _) = True
isNeutral (ApplyE e _) = isNeutral e
isNeutral (ApplyMultiE e _) = isNeutral e
isNeutral (Proj1E e) = isNeutral e
isNeutral (Proj2E e) = isNeutral e
isNeutral (TypeE _ _ _) = True
isNeutral (DataE _ _) = True
isNeutral _ = False

substitute :: [(Name, Expr)] -> Expr -> Expr
substitute [] e = e
substitute ((x, v) : ms) e = substitute ms (substitute1 x v e)

substitute1 :: Name -> Expr -> Expr -> Expr
substitute1 x v e@(VarE y) | x == y    = v
                          | otherwise = e
substitute1 x v e@(PiE y e1 e2) | x == y    = e
                               | otherwise = PiE y (substitute1 x v e1) (substitute1 x v e2)
substitute1 x v e@(LambdaE y e1) | x == y    = e
                                | otherwise = LambdaE y (substitute1 x v e1)
substitute1 x v (ApplyMultiE e es) = ApplyMultiE (substitute1 x v e) (map (substitute1 x v) es)
substitute1 x v (ApplyE e1 e2) = ApplyE (substitute1 x v e1) (substitute1 x v e2)
substitute1 x v e@(SigmaE y e1 e2) | x == y    = e
                                  | otherwise = SigmaE y (substitute1 x v e1) (substitute1 x v e2)
substitute1 x v (PairE e1 e2) = PairE (substitute1 x v e1) (substitute1 x v e2)
substitute1 x v (Proj1E e1) = Proj1E (substitute1 x v e1)
substitute1 x v (Proj2E e1) = Proj2E (substitute1 x v e1)
substitute1 x v (TypeE n ts is) = TypeE n (map (substitute1 x v) ts) (map (substitute1 x v) is)
substitute1 x v (DataE n xs) = DataE n (map (substitute1 x v) xs)
substitute1 x v (CaseE ts mcs) = CaseE (map (\(e, t) -> (substitute1 x v e, substitute1 x v t)) ts) (map (\(ps, b) -> (map (substitutePat1 x v) ps, substitute1 x v b)) mcs)
substitute1 _ _ e = e

substituteWithTelescope :: Telescope -> [TVal] -> Telescope -> Telescope
substituteWithTelescope [] [] rs = rs
substituteWithTelescope ((n, _):ts) (x:xs) rs =
  let ts' = map (\(n2, t) -> (n2, substitute1 n x t)) ts
      rs' = map (\(n2, t) -> (n2, substitute1 n x t)) rs in
    substituteWithTelescope ts' xs rs'

substitutePat :: [(Name, Expr)] -> Pattern -> Pattern
substitutePat [] p = p
substitutePat ((x, v) : ms) p = substitutePat ms (substitutePat1 x v p)

substitutePat1 :: Name -> Expr -> Pattern -> Pattern
substitutePat1 x v p@(PatVar y) = p
substitutePat1 x v (DataPat c ps) = DataPat c (map (substitutePat1 x v) ps)
substitutePat1 x v (ValuePat e) = ValuePat (substitute1 x v e)

--- Type-checking for inductive patterns

checkPattern :: Env -> [(Expr, TVal)] -> [Pattern] -> CheckM ([Pattern], [(Name, TVal)], [(Name, Expr)])
checkPattern env cs ps = do
  (ps', tRet, us, vs) <- checkPattern' env cs ps [] [] [] []
  vRet <- unify us
  mapM_ (\(x, y) ->
           if x == y
             then return ()
             else throwError (Default "value pattern cannot unified"))
    (map (\(x, y) -> (substitute vRet x, substitute vRet y)) vs)
  return (ps', map (\(s, t) -> (s, substitute vRet t)) tRet, vRet)

checkPattern' :: Env -> [(Expr, TVal)] -> [Pattern] -> [Pattern] -> [(Name, TVal)] -> [(Expr, Expr)] -> [(Expr, Expr)] -> CheckM ([Pattern], [(Name, TVal)], [(Expr, Expr)], [(Expr, Expr)])
checkPattern' _ [] [] pat ret us vs = return (pat, ret, us, vs)
checkPattern' env (_ : cs) (Wildcard : ps) pat ret us vs = throwError (Default "cannot reach here1")
checkPattern' env ((e, a) : cs) (PatVar x : ps) pat ret us vs =
  checkPattern' env cs ps (pat ++ [PatVar x]) (ret ++ [(x, a)]) (us ++ [(e, VarE x)]) vs
checkPattern' env ((e, a) : cs) (ValuePat v : ps) pat ret us vs = do
  v' <- check (addToTEnv env ret) v a
  checkPattern' env cs ps (pat ++ [ValuePat v']) ret us (vs ++ [(e, v')])
checkPattern' env ((e, a) : cs) (DataPat c qs : ps) pat ret us vs = do
  a' <- evalWHNF env a
  case a' of
    TypeE _ ats ais -> do
      (tts, xts, b) <- getFromCEnv env c
      (env', ats') <- checkTelescope env ats tts
      let xts' = map (\(s, e) -> (VarE s, e)) xts
      (qs', ret', us', vs') <- checkPattern' env xts' qs [] ret us vs
      let b' = (substitute ((zip (map fst tts) ats') ++ (zip (map fst xts) (map fst xts'))) b)
      case b' of
        TypeE _ bts bis -> do
          (env', bts') <- checkTelescope env bts tts
          checkPattern' env cs ps (pat ++ [DataPat c qs']) ret' (us' ++ [(e, DataE c (map fst xts'))] ++ zip ais bis) vs'
        _ -> throwError (Default "")
    _ -> throwError (Default "")

unify :: [(Expr, Expr)] -> CheckM [(Name, Expr)]
unify [] = return []
unify ((VarE s@('$' : _), e) : us) = ((s, e) :) <$> unify (map (\(x, y) -> (substitute1 s e x, substitute1 s e y)) us) -- replace wildcard
unify ((e, VarE s@('$' : _)) : us) = ((s, e) :) <$> unify (map (\(x, y) -> (substitute1 s e x, substitute1 s e y)) us) -- replace wildcard
unify ((VarE s, e) : us) = ((s, e) :) <$> unify (map (\(x, y) -> (substitute1 s e x, substitute1 s e y)) us) -- TODO: cycle check
unify ((e, VarE s) : us) = ((s, e) :) <$> unify (map (\(x, y) -> (substitute1 s e x, substitute1 s e y)) us) -- TODO: cycle check
unify ((DataE c1 as1, DataE c2 as2) : us) =
  if c1 == c2
    then unify (zip as1 as2 ++ us)
    else throwError (Default "cannot unified")
unify us = throwError (Default ("unify should not reach here:" ++ show us))

-- flexible :: [Pattern] -> Context -> [Name]
-- flexible [] [] = []
-- flexible (ValuePat _ : ps) ((x, _) : delta) = x : flexible ps delta
-- flexible (_ : ps) (_ : delta) = flexible ps delta

-- isFlexible :: Name -> [Name] -> Bool
-- isFlexible x zeta = elem x zeta

-- isFree :: Name -> Expr -> Bool
-- isFree _ _ = False -- TODO: this function is undefined

-- isAccecible :: Name -> [Pattern] -> Bool
-- isAccecible x [] = False
-- isAccecible x (p : ps) = isAccecible1 x p || isAccecible x ps

-- isAccecible1 :: Name -> Pattern -> Bool
-- isAccecible1 x (PatVar y) | x == y = True
-- isAccecible1 _ (PatVar _) = False
-- isAccecible1 x (DataPat _ ps) = isAccecible x ps
-- isAccecible1 x (ValuePat _) = False
     
---
--- Sample programs without pattern matching
---

--(define (id (A : (Universe 0)) (x : A)) : A
--  x)
idDef :: TopExpr
idDef = DefFunE "id"
  [("A", UniverseE 0), ("x", VarE "A")]
  (VarE "A")
  (VarE "x")

--(define (comp (A : (Universe 0)) (B : (Universe 0)) (C : B -> (Universe 0)) (f : (Π (b : B) (C b))) (g : A -> B) (a : A)) : (C (g a))
--  (f (g a)))
compDef :: TopExpr
compDef = DefFunE "comp"
  [("A", UniverseE 0), ("B", UniverseE 0), ("C", ArrowE (VarE "B") (UniverseE 0)), ("f", PiE "x" (VarE "B") (ApplyE (VarE "C") (VarE "x"))), ("g", ArrowE (VarE "A") (VarE "B")), ("x", VarE "A")]
  (ApplyE (VarE "C") (ApplyE (VarE "g") (VarE "x")))
  (ApplyE (VarE "f") (ApplyE (VarE "g") (VarE "x")))

---
--- Sample programs with inductive data
---

--(data Nat {} {}
--  {[zero : Nat]
--   [suc (_ : Nat) : Nat]})
natDef :: TopExpr
natDef = DataDecE "Nat" [] []
  [("zero", [], TypeE "Nat" [] []),
   ("suc", [("_", TypeE "Nat" [] [])], TypeE "Nat" [] [])]

-- (define z : Nat <zero>)
zeroDef :: TopExpr
zeroDef = DefE "z"
  (TypeE "Nat" [] [])
  (DataE "zero" [])

-- (define one : Nat <suc <zero>>)
oneDef :: TopExpr
oneDef = DefE "one"
  (TypeE "Nat" [] [])
  (DataE "suc" [DataE "zero" []])

--(data Eq {(A : (Universe 0)) (x : A)} {A}
--  {[refl  : (Eq A x x)]})
eqDef :: TopExpr
eqDef = DataDecE "Eq" [("A", UniverseE 0), ("x", VarE "A")] [("_", VarE "A")]
  [("refl", [], TypeE "Eq" [VarE "A", VarE "x"] [VarE "x"])]

-- (define r : <Eq {Nat <zero>} {<zero>}>
--   <refl>)
reflDef :: TopExpr
reflDef = DefE "r"
  (TypeE "Eq" [TypeE "Nat" [] [], DataE "zero" []] [DataE "zero" []])
  (DataE "refl" [])

-- (define ir : <Eq {Nat <zero>} {<suc <zero>>}>
--   <refl>)
iReflDef :: TopExpr
iReflDef = DefE "ir"
  (TypeE "Eq" [TypeE "Nat" [] [], DataE "zero" []] [DataE "suc" [DataE "zero" []]])
  (DataE "refl" [])

---
--- Sample programs with pattern matching
---

--(define (plus (x : Nat) (y : Nat)) : Nat
--  {[[<zero> $n] n]
--   [[<suc $m> $n] <suc (plus m n)>]})
plusDef :: TopExpr
plusDef = DefCaseE "plus" [("x", TypeE "Nat" [] []), ("y", TypeE "Nat" [] [])] (TypeE "Nat" [] [])
  [([DataPat "zero" [], PatVar "n"], VarE "n"),
   ([DataPat "suc" [(PatVar "m")], PatVar "n"], DataE "suc" [ApplyMultiE (VarE "plus") [VarE "m", VarE "n"]])]

--(define (cong (A : (Universe 0)) (B : (Universe 0)) (f : A -> B) (x : A) (y : A) (_ : (Eq A x y))) : (Eq B (f x) (f y))
--  {[[_ _ _ _ _ <refl>] <refl>]})
congDef :: TopExpr
congDef = DefCaseE "cong" [("A", (UniverseE 0)), ("B", (UniverseE 0)), ("f", ArrowE (VarE "A") (VarE "B")), ("x", VarE "A"), ("y", VarE "A"), ("_", TypeE "Eq" [VarE "A", VarE "x"] [VarE "y"])] (TypeE "Eq" [VarE "B", ApplyE (VarE "f") (VarE "x")] [ApplyE (VarE "f") (VarE "y")])
  [([Wildcard, Wildcard, Wildcard, Wildcard, Wildcard, DataPat "refl" []], DataE "refl" [])]

--(define (plusZero (n : Nat)) : (Eq Nat (plus n <zero>) n)
--  {[<zero> <refl>]
--   [<suc $m> (cong (lambda [$k] <suc k>) (plus m <zero>) m (plusZero m))]})
plusZeroDef :: TopExpr
plusZeroDef = DefCaseE "plusZero" [("n", TypeE "Nat" [] [])] (TypeE "Eq" [TypeE "Nat" [] [], ApplyMultiE (VarE "plus") [(VarE "n"), (DataE "zero" [])]] [VarE "n"])
  [([DataPat "zero" []], DataE "refl" []),
   ([DataPat "suc" [PatVar "m"]], ApplyMultiE (VarE "cong") [TypeE "Nat" [] [], TypeE "Nat" [] [], LambdaE "k" (DataE "suc" [VarE "k"]), ApplyMultiE (VarE "plus") [VarE "m", DataE "zero" []], VarE "m", ApplyMultiE (VarE "plusZero") [VarE "m"]])]

-- (define (axiomK (A : (Universe 0)) (a : A) (P : <Eq {A a} {a}> -> (Universe 0)) (p : (P <refl>)) (e : <Eq {A a} {a}>)) : (P e)
--   {[[_ _ _ _ <refl>] p]})
axiomKDef :: TopExpr
axiomKDef = DefCaseE "axiomK" [("A", (UniverseE 0)), ("a", (VarE "A")), ("P", (ArrowE (TypeE "Eq" [(VarE "A"), (VarE "a")] [(VarE "a")]) (UniverseE 0))), ("p", (ApplyE (VarE "P") (DataE "refl" []))), ("e", (TypeE "Eq" [(VarE "A"), (VarE "a")] [(VarE "a")]))] (ApplyE (VarE "P") (VarE "e"))
  [([Wildcard, Wildcard, Wildcard, Wildcard, DataPat "refl" []], VarE "p")]

--(data Lte {} {Nat Nat}
--  {[lz (n : Nat) : (Lte <zero> n)]
--   [ls (m : Nat) (n : Nat) (_ : (Lte m n)) : (Lte <suc m> <suc n>)]})
lteDef :: TopExpr
lteDef = DataDecE "Lte" [] [("_", TypeE "Nat" [] []), ("_", TypeE "Nat" [] [])]
  [("lz", [("n", TypeE "Nat" [] [])], TypeE "Lte" [] [DataE "zero" [], VarE "n"]),
   ("ls", [("m", TypeE "Nat" [] []), ("n", TypeE "Nat" [] []), ("_", TypeE "Lte" [] [VarE "m", VarE "n"])], (TypeE "Lte" [] [DataE "suc" [VarE "m"], DataE "suc" [VarE "n"]]))]

--(define (antisym (m : Nat) (n : Nat) (_ : (Lte m n)) (_ : (Lte n m))) : (Eq Nat m n)
--  {[[<zero> <zero> <lz #<zero>> <lz #<zero>>] <refl>]
--   [[<suc $m'> <suc $n'> <ls #m' #n' $x> <ls #n' #m' $y>] (cong Nat Nat (lambda [$k] <suc k>) m' n' (antisym m' n' x y))]})
antisymDef :: TopExpr
antisymDef = DefCaseE "antisym" [("m", TypeE "Nat" [] []), ("n", TypeE "Nat" [] []), ("_", TypeE "Lte" [] [VarE "m", VarE "n"]), ("_", TypeE "Lte" [] [VarE "n", VarE "m"])] (TypeE "Eq" [TypeE "Nat" [] [], VarE "m"] [VarE "n"])
  [([DataPat "zero" [], DataPat "zero" [], DataPat "lz" [ValuePat (DataE "zero" [])], DataPat "lz" [ValuePat (DataE "zero" [])]], DataE "refl" []),
   ([DataPat "suc" [PatVar "m'"], DataPat "suc" [PatVar "n'"], DataPat"ls" [ValuePat (VarE "m'"), ValuePat (VarE "n'"), PatVar "x"], DataPat "ls" [ValuePat (VarE "n'"), ValuePat (VarE "m'"), PatVar "y"]], ApplyMultiE (VarE "cong") [TypeE "Nat" [] [], TypeE "Nat" [] [], LambdaE "k" (DataE "suc" [VarE "k"]), VarE "m'", VarE "n'", ApplyMultiE (VarE "antisym") [VarE "m'", VarE "n'", VarE "x", VarE "y"]])]

--(data (Vec {(A : (Universe 0))} {(_ : Nat)}
--  {[nil  : (Vec A <zero>)]
--   [cons (n : Nat) (_ : A) (_ : (Vec A n)) : (Vec A <suc n>)]})
vecDef :: TopExpr
vecDef = DataDecE "Vec" [("A", (UniverseE 0))] [("_", TypeE "Nat" [] [])]
  [("nil", [], (TypeE "Vec" [VarE "A"] [DataE "zero" []])),
   ("cons", [("n", TypeE "Nat" [] []), ("_", VarE "A"), ("_", TypeE "Vec" [VarE "A"] [VarE "n"])], (TypeE "Vec" [VarE "A"] [DataE "suc" [VarE "n"]]))]
