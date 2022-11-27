{-# Language TypeSynonymInstances, FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, UndecidableInstances, DeriveDataTypeable,
             TypeFamilies, TupleSections, BangPatterns, TemplateHaskell, QuasiQuotes #-}

module Language.EgisonProver.Env
       (
         Env
       , initTopVEnv
       , initTopTEnv
       , initTopDEnv
       , initTopCEnv
       , getFromVEnv
       , getFromTEnv
       , getFromDEnv
       , getConstructors
       , getFromCEnv
       , addToVEnv
       , addToVEnv1
       , addToTEnv
       , addToTEnv1
       ) where

import Language.EgisonProver.AST
import Language.EgisonProver.Monad
import Control.Egison hiding (Pattern)
import qualified Control.Egison as Egison
import Control.Exception.Safe hiding (try)
import Control.Monad.Except

type Env = (VEnv, TEnv, DEnv, CEnv)
type VEnv = [(Name, Expr)] -- Value environment
type TEnv = [(Name, TVal)] -- Type environment
type DEnv = [(Name, (Telescope, Indices, [Name]))] -- Datatype enviroment
type CEnv = [(Name, (Telescope, Telescope, TVal))] -- Constructor enviroment

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
initTopDEnv (DataDecE n ts is cs : rs) = (n, (ts, is, (map (\(c, _, _) -> c) cs))) : (initTopDEnv rs)
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
getFromVEnv (venv, _, _, _) x = case getFromEnv' venv x of
  Nothing -> return Nothing
  (Just e) -> Just <$> alphaConvertion e
     
getFromTEnv :: Env -> Name -> CheckM TVal
getFromTEnv (_, tenv, _, _) x = getFromEnv tenv x >>= alphaConvertion
     
getFromDEnv :: Env -> Name -> CheckM (Telescope, Indices)
getFromDEnv (_, _, denv, _) x = do
  (ts, is, _) <- getFromEnv denv x
  tns <- mapM addFresh (map fst ts)
  ins <- mapM addFresh (map fst is)
  let tms = map (\(s, s') -> (s, VarE s')) (zip (map fst ts) tns)
  let ims = map (\(s, s') -> (s, VarE s')) (zip (map fst is) ins)
  return (zip tns (map (substitute tms) (map snd ts)), zip ins (map (substitute (tms ++ ims)) (map snd is)))
     
getConstructors :: Env -> Name -> CheckM ([Name])
getConstructors (_, _, denv, _) x = do
  (_, _, ns) <- getFromEnv denv x
  return ns
     
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

alphaConvertion :: Expr -> CheckM Expr
alphaConvertion (PiE x e1 e2) = do
  x' <- addFresh x
  PiE x' <$> alphaConvertion (substitute1 x (VarE x') e1) <*> alphaConvertion (substitute1 x (VarE x') e2)
alphaConvertion (LambdaMultiE xs e) = do
  xs' <- mapM addFresh xs
  LambdaMultiE xs' <$> alphaConvertion (substitute (zip xs (map VarE xs')) e)
alphaConvertion (LambdaE x e) = do
  x' <- addFresh x
  LambdaE x' <$> alphaConvertion (substitute1 x (VarE x') e)
alphaConvertion (SigmaE x e1 e2) = do
  x' <- addFresh x
  SigmaE x' <$> alphaConvertion (substitute1 x (VarE x') e1) <*> alphaConvertion (substitute1 x (VarE x') e2)
--alphaConvertion (CaseE ts mcs) = undefined -- TODO
alphaConvertion (ApplyMultiE e es) = ApplyMultiE <$> alphaConvertion e <*> mapM alphaConvertion es
alphaConvertion (ApplyE e1 e2) = ApplyE <$> alphaConvertion e1 <*> alphaConvertion e2
alphaConvertion (PairE e1 e2) = PairE <$> alphaConvertion e1 <*> alphaConvertion e2
alphaConvertion (Proj1E e1) = Proj1E <$> alphaConvertion e1
alphaConvertion (Proj2E e1) = Proj2E <$> alphaConvertion e1
alphaConvertion (TypeE n ts is) = TypeE n <$> (mapM alphaConvertion ts) <*> (mapM alphaConvertion is)
alphaConvertion (DataE n xs) = DataE n <$> (mapM alphaConvertion xs)
alphaConvertion e = return e
