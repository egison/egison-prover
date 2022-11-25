{-# Language TypeSynonymInstances, FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, UndecidableInstances, DeriveDataTypeable,
             TypeFamilies, TupleSections, BangPatterns, TemplateHaskell, QuasiQuotes #-}

module Language.EgisonProver.Check
       (
       -- * Check
         checkTopExpr
       ) where

import Language.EgisonProver.AST
import Language.EgisonProver.Env
import Language.EgisonProver.Monad

import Control.Exception.Safe hiding (try)
import Control.Monad.Except
import Control.Monad.Trans.State.Strict


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
                   (p', tRet, vRet) <- runCheckPatternM (checkPattern env ts p)
                   b' <- check (addToTEnv env tRet) b (substitute vRet a)
                   return (p', b')
               ) mcs
--  checkCoverage env ts (map fst mcs)
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
checkTelescope _ _ _ = throwError (Default "checkTelescope: should not reach here")

infer :: Env -> Expr -> CheckM (Expr, Expr)
infer env e@(VarE x) = do
  a <- getFromTEnv env x
  return (a, e)
infer env (ApplyMultiE (VarE s) as) = do
  (a, e) <- infer env (foldl (\f' a -> ApplyE f' a) (VarE s) as)
  e' <- sugarToApplyMulti [] e
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
infer _ e@(TypeE _ _ _) = do
  return (UniverseE 0, e)
infer _ e = throwError (Default ("infer not implemented:" ++ show e))

sugarToApplyMulti :: [Expr] -> Expr -> CheckM Expr
sugarToApplyMulti as (VarE s) = return (ApplyMultiE (VarE s) as)
sugarToApplyMulti as (ApplyE f a) = sugarToApplyMulti (a : as) f
sugarToApplyMulti _ _ = throwError (Default "sugarToApplyMulti: should not reach here")

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
areConvertible _ _ _ _ = throwError (Default "areConvertible: should not reach here")

isConvertible :: Env -> Expr -> Expr -> Expr -> CheckM ()
isConvertible env s t a = do
  s' <- evalWHNF env s
  t' <- evalWHNF env t
  a' <- evalWHNF env a
  isConvertible' env s' t' a'

isConvertible' :: Env -> Expr -> Expr -> Expr -> CheckM ()
isConvertible' _ (UniverseE i) (UniverseE j) UniverseAlphaE =
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
isConvertible' _ _ _ UnitTypeE = return ()
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
isConvertible' env s t _ = do
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
    SigmaE _ b _ -> do
      return b
    _ -> throwError (Default "isEqual proj1")
isEqual env (Proj2E s) (Proj2E t) = do
  a <- isEqual env s t
  a' <- evalWHNF env a
  case a' of
    SigmaE x _ c -> do
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
    _ -> evalWHNF env (foldl (\f a -> ApplyE e a) e' es)
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
evalMCs _ _ [] = return Nothing
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


--- Type-checking for inductive patterns

checkPattern :: Env -> [(Expr, TVal)] -> [Pattern] -> CheckPatternM ([Pattern], [(Name, TVal)], [(Name, Expr)])
checkPattern env cs ps = do
  (ps', tRet, us, vs) <- checkPattern' env cs ps [] [] [] []
  vRet <- unify us
  mapM_ (\(x, y) ->
           if x == y
             then return ()
             else lift $ throwError (Default "value pattern cannot unified"))
    (map (\(x, y) -> (substitute vRet x, substitute vRet y)) vs)
  return (ps', map (\(s, t) -> (s, substitute vRet t)) tRet, vRet)

checkPattern' :: Env -> [(Expr, TVal)] -> [Pattern] -> [Pattern] -> [(Name, TVal)] -> [(Expr, Expr)] -> [(Expr, Expr)] -> CheckPatternM ([Pattern], [(Name, TVal)], [(Expr, Expr)], [(Expr, Expr)])
checkPattern' _ [] [] pat ret us vs = return (pat, ret, us, vs)
checkPattern' env ((e, a) : cs) (PatVar x : ps) pat ret us vs =
  checkPattern' env cs ps (pat ++ [PatVar x]) (ret ++ [(x, a)]) (us ++ [(e, VarE x)]) vs
checkPattern' env ((e, a) : cs) (ValuePat v : ps) pat ret us vs = do
  v' <- lift $ check (addToTEnv env ret) v a
  checkPattern' env cs ps (pat ++ [ValuePat v']) ret us (vs ++ [(e, v')])
checkPattern' env ((e, a) : cs) (DataPat c qs : ps) pat ret us vs = do
  a' <- lift $ evalWHNF env a
  case a' of
    TypeE _ ats ais -> do
      (tts, xts, b) <- lift $ getFromCEnv env c
      (env', ats') <- lift $ checkTelescope env ats tts
      let xts' = map (\(s, e) -> (VarE s, e)) xts
      (qs', ret', us', vs') <- checkPattern' env' xts' qs [] ret us vs
      let b' = (substitute ((zip (map fst tts) ats') ++ (zip (map fst xts) (map fst xts'))) b)
      case b' of
        TypeE _ bts bis -> do
          _ <- lift $ checkTelescope env bts tts
          checkPattern' env cs ps (pat ++ [DataPat c qs']) ret' (us' ++ [(e, DataE c (map fst xts'))] ++ zip ais bis) vs'
        _ -> throwError (PMError "")
    _ -> throwError (PMError "")
checkPattern' _ _ _ _ _ _ _ = lift $ throwError (Default "checkPattern': should not reach here")

unify :: [(Expr, Expr)] -> CheckPatternM [(Name, Expr)]
unify [] = return []
unify ((x@(VarE _), y) : _) | x == y = throwError (PMError ("unify deletion rule: " ++ show (x, y)))
unify ((VarE s@('$' : _), e) : us) = ((s, e) :) <$> unify (map (\(x, y) -> (substitute1 s e x, substitute1 s e y)) us) -- replace wildcard
unify ((e, VarE s@('$' : _)) : us) = ((s, e) :) <$> unify (map (\(x, y) -> (substitute1 s e x, substitute1 s e y)) us) -- replace wildcard
unify ((VarE s, e) : us) = ((s, e) :) <$> unify (map (\(x, y) -> (substitute1 s e x, substitute1 s e y)) us) -- TODO: cycle check
unify ((e, VarE s) : us) = ((s, e) :) <$> unify (map (\(x, y) -> (substitute1 s e x, substitute1 s e y)) us) -- TODO: cycle check
unify ((DataE c1 as1, DataE c2 as2) : us) =
  if c1 == c2
    then unify (zip as1 as2 ++ us)
    else throwError (PMError "cannot unified")
unify us = lift $ throwError (Default ("unify should not reach here:" ++ show us))

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

checkCoverage :: Env -> [(Expr, TVal)] -> [[Pattern]] -> CheckM ()
checkCoverage env ts pss = undefined -- checkCoverage' env [(map (\_ -> Wildcard) ts)] ts pss

           
isAbsurd :: Env -> [(Expr, TVal)] -> [Pattern] -> CheckM Bool
isAbsurd env ts ps = do
  ret <- runExceptT (checkPattern env ts ps)
  case ret of
    Left _ -> return False
    Right _ -> return True

simplifyPattern :: Pattern -> PPattern
simplifyPattern (PatVar _) = PWildcard
simplifyPattern (ValuePat _) = PWildcard
simplifyPattern (DataPat c ps) = PDataPat c (map simplifyPattern ps)
               
makeCaseTree :: Env -> [[Pattern]] -> [[PPattern]]
makeCaseTree env pss =
  makeCaseTree' env (map (\ps -> (map simplifyPattern ps)) pss)

makeCaseTree' :: Env -> [[PPattern]] -> [[PPattern]]
makeCaseTree' = undefined
