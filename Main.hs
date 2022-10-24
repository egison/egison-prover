{-# Language TypeSynonymInstances, FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, UndecidableInstances, DeriveDataTypeable,
             TypeFamilies, TupleSections, BangPatterns, TemplateHaskell, QuasiQuotes #-}


module Main where

import Control.Exception.Safe
import Control.Monad.Except
import Control.Egison hiding (Pattern)

main :: IO ()
main = do
  let topExprs = map desugarTopExpr [idDef, compDef]
  let gammaT = initTopTEnv topExprs
  let gammaD = initTopDEnv topExprs
  let gammaC = initTopCEnv topExprs
  let gamma = (gammaT, gammaD, gammaC)
  ret <- runCheckM (checkTopExpr gamma (desugarTopExpr idDef))
  case ret of
    Left err -> print err
    Right expr -> print (show expr)
  ret <- runCheckM (checkTopExpr gamma (desugarTopExpr compDef))
  case ret of
    Left err -> print err
    Right expr -> print (show expr)
  
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

type CheckM = ExceptT PwlError IO

runCheckM :: CheckM a -> IO (Either PwlError a)
runCheckM = runExceptT

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
  | CaseE [Expr] [([Pattern], Expr)]
 deriving Show

data Pattern
  = PatVar Name
  | ConsPat Name [Pattern]
  | InaccessiblePat Expr
 deriving Show

type TVal = Expr
type Val = Expr

type Env = (TEnv, DEnv, CEnv)
type TEnv = [(Name, TVal)] -- Type environment
type DEnv = [(Name, (Telescope, Indices))] -- Datatype enviroment
type CEnv = [(Name, (Telescope, Telescope, TVal))] -- Constructor enviroment
  
type Context = [(Name, TVal)]
type Telescope = [(Name, TVal)]
type Indices = [(Name, TVal)]

data Kind
  = ValueK
  | DatatypeK
  | ConstructorK

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
getFromEnv gamma x =
  match dfs gamma (List (Pair Eql Something))
    [[mc| _ ++ (#x, $t) : _ -> return t |],
     [mc| _ -> throw (UnboundVariable x) |]]

getFromTEnv :: Env -> Name -> CheckM TVal
getFromTEnv (tenv, _, _) x = getFromEnv tenv x
     
getFromDEnv :: Env -> Name -> CheckM (Telescope, Indices)
getFromDEnv (_, denv, _) x = getFromEnv denv x
     
getFromCEnv :: Env -> Name -> CheckM (Telescope, Telescope, TVal)
getFromCEnv (_, _, cenv) x = getFromEnv cenv x

addToTEnv :: Env -> Name -> TVal -> Env
addToTEnv (tenv, denv, cenv) x a = (tenv ++ [(x, a)], denv, cenv)
                             
--- Desugar

desugarTopExpr :: TopExpr -> TopExpr
desugarTopExpr (DataDecE n as is cs) =
  let as' = map (\(s, e) -> (s, desugarExpr e)) as
      is' = map (\(s, e) -> (s, desugarExpr e)) is
      cs' = map (\(s, ts, e) -> (s, (map (\(s', e') -> (s', desugarExpr e')) ts), desugarExpr e)) cs
  in DataDecE n as' is' cs'
desugarTopExpr (DefE n t e) =
  let t' = desugarExpr t
      e' = desugarExpr e
  in DefE n t' e'
desugarTopExpr (DefFunE n as t e) =
  let t' = foldr (\(s, u) t' -> PiE s u t') t as
      e' = foldr (\(s, _) e' -> LambdaE s e') e as
  in desugarTopExpr (DefE n t' e')
desugarTopExpr (DefCaseE n as t cs) =
  let as' = map (\(s, _) -> VarE s) as
  in desugarTopExpr (DefFunE n as t (CaseE as' cs))
  
desugarExpr :: Expr -> Expr
desugarExpr (ArrowE t1 t2) = desugarExpr (PiE "_" t1 t2)
desugarExpr (LambdaMultiE ns e) = desugarExpr (foldr (\n e' -> LambdaE n e') e ns)
desugarExpr (ApplyMultiE f as) = desugarExpr (foldl (\a f' -> ApplyE f' a) f as)
desugarExpr (PiE n e1 e2) = PiE n (desugarExpr e1) (desugarExpr e2)
desugarExpr (LambdaE n e1) = LambdaE n (desugarExpr e1)
desugarExpr (ApplyE e1 e2) = ApplyE (desugarExpr e1) (desugarExpr e2)
desugarExpr (SigmaE n e1 e2) = SigmaE n (desugarExpr e1) (desugarExpr e2)
desugarExpr (PairE e1 e2) = PairE (desugarExpr e1) (desugarExpr e2)
desugarExpr (Proj1E e1) = Proj1E (desugarExpr e1)
desugarExpr (Proj2E e1) = Proj2E (desugarExpr e1)
desugarExpr (CaseE ts cs) = CaseE (map desugarExpr ts) (map (\(ps, e) -> (map desugarPattern ps, desugarExpr e)) cs)
desugarExpr e = e

desugarPattern :: Pattern -> Pattern
desugarPattern (InaccessiblePat e) = InaccessiblePat (desugarExpr e)
desugarPattern (ConsPat n ps) = ConsPat n (map desugarPattern ps)
desugarPattern p = p
                
--- Type checking

checkTopExpr :: Env -> TopExpr -> CheckM TopExpr
checkTopExpr gamma (DefE n t e) = do
  e' <- check gamma e t
  return (DefE n t e')

check :: Env -> Expr -> Expr -> CheckM Expr
check gamma (LambdaE x e) a = do
  a' <- evalWHNF a
  case a' of
    PiE y b c -> do
      e' <- check (addToTEnv gamma x b) e c
      return (LambdaE x e')
    _ -> throw (TypeDoesNotMatch (LambdaE x e) a')
check gamma (PairE e1 e2) a = do
  a' <- evalWHNF a
  case a' of
    SigmaE x b c -> do
      s <- check gamma e1 b
      t <- check gamma e2 (substitute1 x s c)
      return (PairE s t)
    _ -> throw (TypeDoesNotMatch (PairE e1 e2) a')
check gamma e a = do
  (b, t) <- infer gamma e
  isSubtype gamma a b
  return t

infer :: Env -> Expr -> CheckM (Expr, Expr)
infer gamma e@(VarE x) = do
  a <- getFromTEnv gamma x
  return (a, e)
infer gamma (ApplyE e1 e2) = do
  (a, s) <- infer gamma e1
  a' <- evalWHNF a
  case a' of
    PiE x b c -> do
      t <- check gamma e2 b
      return (substitute1 x t c, ApplyE s t)
    _ -> throw (ShouldBe "function" e1)
infer gamma (Proj1E e) = do
  (a, t) <- infer gamma e
  a' <- evalWHNF a
  case a' of
    SigmaE _ b _ -> do
      return (b, Proj1E t)
    _ -> throw (ShouldBe "pair" e)
infer gamma (Proj2E e) = do
  (a, t) <- infer gamma e
  a' <- evalWHNF a
  case a' of
    SigmaE x _ c -> do
      return (substitute1 x (Proj1E t) c, Proj2E t)
    _ -> throw (ShouldBe "pair" e)
infer gamma (PiE x e1 e2) = do
  (c1, a) <- infer gamma e1
  (c2, b) <- infer (addToTEnv gamma x a) e2
  c1' <- evalWHNF c1
  c2' <- evalWHNF c2
  case (c1', c2') of
    (UniverseE i, UniverseE j) -> do
      return (UniverseE (max i j), PiE x a b)
    _ -> throw (Default "")
infer gamma (SigmaE x e1 e2) = do
  (c1, a) <- infer gamma e1
  (c2, b) <- infer (addToTEnv gamma x a) e2
  c1' <- evalWHNF c1
  c2' <- evalWHNF c2
  case (c1', c2') of
    (UniverseE i, UniverseE j) -> do
      return (UniverseE (max i j), SigmaE x a b)
    _ -> throw (Default "")
infer _ e@UnitE = do
  return (UnitTypeE, e)
infer _ e@UnitTypeE = do
  return (UniverseE 0, e)
infer _ e@(UniverseE n) = do
  return (UniverseE (n + 1), e)
infer _ e@(TypeE n ts is) = do
  undefined
infer _ e@(DataE n xs) = do
  undefined
infer _ _ = throw (Default "not implemented")

isSubtype :: Env -> Expr -> Expr -> CheckM ()
isSubtype gamma a b = do
  a' <- evalWHNF a
  b' <- evalWHNF b
  isSubtype' gamma a' b'

isSubtype' :: Env -> Expr -> Expr -> CheckM ()
isSubtype' _ (UniverseE i) (UniverseE j) =
  if i + 1 == j then return () else throw (Default "")
isSubtype' gamma (PiE x a1 b1) (PiE y a2 b2) =
  if x == y
    then do
      isConvertible gamma a1 a2 UniverseAlphaE
      isSubtype (addToTEnv gamma x a1) b1 b2
    else throw (NotConvertible (PiE x a1 b1) (PiE y a2 b2))
isSubtype' gamma (SigmaE x a1 b1) (SigmaE y a2 b2) =
  if x == y
    then do
      isConvertible gamma a1 a2 UniverseAlphaE
      isSubtype (addToTEnv gamma x a1) b1 b2
    else throw (NotConvertible (SigmaE x a1 b1) (SigmaE y a2 b2))
isSubtype' gamma a b = isConvertible' gamma a b UniverseAlphaE

isConvertible :: Env -> Expr -> Expr -> Expr -> CheckM ()
isConvertible gamma s t a = do
  s' <- evalWHNF s
  t' <- evalWHNF t
  a' <- evalWHNF a
  isConvertible' gamma s' t' a'

isConvertible' :: Env -> Expr -> Expr -> Expr -> CheckM ()
isConvertible' gamma (UniverseE i) (UniverseE j) UniverseAlphaE =
  if i == j then return () else throw (NotConvertible (UniverseE i) (UniverseE j))
isConvertible' gamma (PiE x a1 b1) (PiE y a2 b2) UniverseAlphaE =
  if x == y
    then do
      isConvertible gamma a1 a2 UniverseAlphaE
      isConvertible (addToTEnv gamma x a1) b1 b2 UniverseAlphaE
    else throw (NotConvertible (PiE x a1 b1) (PiE y a2 b2))
isConvertible' gamma (SigmaE x a1 b1) (SigmaE y a2 b2) UniverseAlphaE =
  if x == y
    then do
      isConvertible gamma a1 a2 UniverseAlphaE
      isConvertible (addToTEnv gamma x a1) b1 b2 UniverseAlphaE
    else throw (NotConvertible (SigmaE x a1 b1) (SigmaE y a2 b2))
isConvertible' gamma s t UnitTypeE = return ()
isConvertible' gamma s t (PiE x a b) = isConvertible (addToTEnv gamma x a) (ApplyE s (VarE x)) (ApplyE t (VarE x)) b
isConvertible' gamma s t (SigmaE x a b) = do
  isConvertible gamma (Proj1E s) (Proj1E t) a
  isConvertible gamma (Proj2E s) (Proj2E t) (substitute1 x (Proj1E s) b)
isConvertible' gamma s t a = do
  if isNeutral s && isNeutral t
    then do
      _ <- isEqual gamma s t
      return ()
    else throw (Default "")

isEqual :: Env -> Expr -> Expr -> CheckM Expr
isEqual gamma (VarE x) (VarE y) =
  if x == y
    then do
      a <- getFromTEnv gamma x
      return a
    else throw (Default "")
isEqual gamma (ApplyE s1 t1) (ApplyE s2 t2) = do
  a <- isEqual gamma s1 s2
  a' <- evalWHNF a
  case a' of
    PiE x b c -> do
      isConvertible gamma t1 t2 b
      return (substitute1 x t1 c)
    _ -> throw (Default "")
isEqual gamma (Proj1E s) (Proj1E t) = do
  a <- isEqual gamma s t
  a' <- evalWHNF a
  case a' of
    SigmaE x b c -> do
      return b
    _ -> throw (Default "")
isEqual gamma (Proj2E s) (Proj2E t) = do
  a <- isEqual gamma s t
  a' <- evalWHNF a
  case a' of
    SigmaE x b c -> do
      return (substitute1 x (Proj1E s) c)
    _ -> throw (Default "")

evalWHNF :: Expr -> CheckM Expr
--evalWHNF (VarE n) = undefined
evalWHNF (ApplyE e1 e2) = do
  e1' <- evalWHNF e1
  case e1' of
    LambdaE x b -> return (substitute1 x e2 b)
    _ -> return (ApplyE e1' e2)
evalWHNF (Proj1E e) = do
  e' <- evalWHNF e
  case e' of
    PairE e1 _ -> evalWHNF e1
    _ -> return e'
evalWHNF (Proj2E e) = do
  e' <- evalWHNF e
  case e' of
    PairE _ e2 -> evalWHNF e2
    _ -> return e'
evalWHNF e = return e

isNeutral :: Expr -> Bool
isNeutral (VarE _) = True
isNeutral (ApplyE e _) = isNeutral e
isNeutral (Proj1E e) = isNeutral e
isNeutral (Proj2E e) = isNeutral e
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
substitute1 x v (ApplyE e1 e2) = ApplyE (substitute1 x v e1) (substitute1 x v e2)
substitute1 x v e@(SigmaE y e1 e2) | x == y    = e
                                  | otherwise = SigmaE y (substitute1 x v e1) (substitute1 x v e2)
substitute1 x v (PairE e1 e2) = PairE (substitute1 x v e1) (substitute1 x v e2)
substitute1 x v (Proj1E e1) = Proj1E (substitute1 x v e1)
substitute1 x v (Proj2E e1) = Proj2E (substitute1 x v e1)
substitute1 _ _ e = e

substitutePat :: [(Name, Pattern)] -> Pattern -> Pattern
substitutePat [] p = p
substitutePat ((x, q) : ms) p = substitutePat ms (substitutePat1 (x, q) p)

substitutePat1 :: (Name, Pattern) -> Pattern -> Pattern
substitutePat1 (x, q) p@(PatVar y) | x == y = q
                                   | otherwise = p
substitutePat1 (x, q) (ConsPat c ps) = ConsPat c (map (substitutePat1 (x, q)) ps)
substitutePat1 _ p = p

--- Type-checking for inductive patterns

type ContextMapping = ([(Name, Pattern)], Context, Context)

split :: [Pattern] -> Context -> CheckM (Maybe ContextMapping)
split ps delta = undefined
--  match (zip ps delta) (List (Pair PatternM (Pair Something Something)))
--    [[mc| $hs ++ (consPat $c $qs, ($x, $a)) :: $ts -> do
--        let (ps1, delta1) = unzip hs
--        let (ps2, delta2) = unzip ts
--        undefined
--        cT <- getType c
--        flexible (ps1 ++ qs) (delta1 ++ theta)
--        undefined
--        return (Just (undefined, undefined, delta))
--        |],
--     [mc| _ -> return Nothing|]]

updatePat :: ContextMapping -> [Pattern] -> CheckM [Pattern]
updatePat (ms, _, delta) ps = updatePat' (map (substitutePat ms) (map (\(q, _) -> PatVar q) delta)) ps

updatePat' :: [Pattern] -> [Pattern] -> CheckM [Pattern]
updatePat' [] [] = return []
updatePat' (sigma : sigmas) (p : ps) = do
  q1 <- updatePat1 sigma p
  q2 <- updatePat' sigmas ps
  return (q1 ++ q2)
 where
  updatePat1 sigma@(PatVar _) p = return [p]
  updatePat1 (InaccessiblePat _) _ = return []
  updatePat1 (ConsPat c sigmas) (ConsPat c' ps) =
    if c == c'
      then updatePat' sigmas ps
      else throw (Default "")

proceed :: [Pattern] -> ContextMapping -> CheckM ([Pattern], ContextMapping)
proceed ps (ms, delta, gamma) = do
  Just (ms', delta', _) <- split ps delta
  ps' <- updatePat (ms', delta', delta) ps
  return (ps', (ms ++ ms', delta', gamma))

proceedMulti :: [Pattern] -> ContextMapping -> CheckM ([Pattern], ContextMapping)
proceedMulti ps sigma@(ms, delta, gamma) = do
  ret <- split ps delta
  case ret of
    Nothing -> return (ps, sigma)
    Just _ -> do
      (ps', sigma') <- proceed ps sigma
      proceedMulti ps' sigma'

checkPats :: [Pattern] -> Context -> CheckM ([Pattern], ContextMapping)
checkPats ps gamma = proceedMulti ps (idContextMapping gamma)

idContextMapping :: Context -> ContextMapping
idContextMapping gamma = ([], gamma, gamma)

flexible :: [Pattern] -> Context -> [Name]
flexible [] [] = []
flexible (InaccessiblePat _ : ps) ((x, _) : delta) = x : flexible ps delta
flexible (_ : ps) (_ : delta) = flexible ps delta

unify :: [Name] -> Context -> [Expr] -> [Expr] -> [Expr] -> CheckM ContextMapping
unify zeta gamma vs ws xi = undefined

unify1 :: [Name] -> Context -> Expr -> Expr -> Expr -> CheckM ContextMapping
unify1 zeta gamma (VarE x) v _ =
  if isFlexible x zeta && not (isFree x v)
    then return ([(x, InaccessiblePat v)], undefined, gamma)
    else throw (Default "")
unify1 zeta gamma (ApplyMultiE (VarE c1) us) (ApplyMultiE (VarE c2) vs) a =
  if c1 == c2
    then do
      -- get the type of the constructor c1
      unify zeta gamma us vs undefined
    else throw (Default "")

isFlexible = undefined
isFree = undefined

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
--- Sample programs with pattern matching
---

--(data Nat {} {}
--  {[zero : Nat]
--   [suc (_ : Nat) : Nat]})
natDef :: TopExpr
natDef = DataDecE "Nat" [] []
  [("zero", [], TypeE "Nat" [] []),
   ("suc", [("_", TypeE "Nat" [] [])], TypeE "Nat" [] [])]

--(data Eq {(A : (Universe 0)) (x : A)} {A}
--  {[refl  : (Eq A x x)]})
eqDef :: TopExpr
eqDef = DataDecE "Eq" [("A", UniverseE 0), ("x", VarE "A")] [("_", VarE "A")]
  [("refl", [], TypeE "Eq" [VarE "A", VarE "x"] [VarE "x"])]

--(def (cong (f : A -> B) (x : A) (y : A) (_ : (Eq A x y))) : (Eq B (f x) (f y))
--  {[[_ _ _ <refl>] <refl>]})
congDef :: TopExpr
congDef = DefCaseE "cong" [("f", ArrowE (VarE "A") (VarE "B")), ("x", VarE "A"), ("y", VarE "A"), ("_", TypeE "Eq" [VarE "A", VarE "x"] [VarE "y"])] (TypeE "Eq" [VarE "B", ApplyE (VarE "f") (VarE "x")] [ApplyE (VarE "f") (VarE "y")])
  [([PatVar "f", ConsPat "refl" []], VarE "refl")]

--(define (plus (_ : Nat) (_ : Nat)) : Nat
--  {[[<zero> $n] n]
--   [[<suc $m> $n] <suc (plus m n)>]})
plusDef :: TopExpr
plusDef = DefCaseE "plus" [("_", TypeE "Nat" [] []), ("_", TypeE "Nat" [] [])] (TypeE "Nat" [] [])
  [([ConsPat "zero" [], PatVar "n"], VarE "n"),
   ([ConsPat "suc" [(PatVar "m")], PatVar "n"], DataE "suc" [ApplyMultiE (VarE "plus") [VarE "m", VarE "n"]])]

--(def (plusZero (n : Nat)) : (Eq Nat (plus n <zero>) n)
--  {[<zero> <refl>]
--   [<suc $m> (cong suc (plusZero m))]})
plusZeroDef :: TopExpr
plusZeroDef = DefCaseE "plusZero" [("n", TypeE "Nat" [] [])] (TypeE "Eq" [TypeE "Nat" [] [], ApplyMultiE (VarE "plus") [(VarE "n"), (DataE "zero" [])]] [VarE "n"])
  [([ConsPat "zero" []], VarE "refl"),
   ([ConsPat "suc" [PatVar "m"]], ApplyMultiE (VarE "cong") [VarE "suc", ApplyE (VarE "plusZero") (VarE "m")])]

--(data Lte {} {Nat Nat}
--  {[lz (y : Nat) : (Lte <zero> y)]
--   [ls (x : Nat) (y : Nat) (_ : (Lte x y)) : (Lte <suc x> <suc y>)]})
lteDef :: TopExpr
lteDef = DataDecE "Lte" [] [("_", TypeE "Nat" [] []), ("_", TypeE "Nat" [] [])]
  [("lz", [("n", TypeE "Nat" [] [])], TypeE "Lte" [] [DataE "zero" [], VarE "n"]),
   ("ls", [("m", TypeE "Nat" [] []), ("n", TypeE "Nat" [] []), ("_", TypeE "Lte" [] [VarE "m", VarE "n"])], (TypeE "Lte" [] [DataE "suc" [VarE "m"], DataE "suc" [VarE "n"]]))]

--(def (antisym (m : Nat) (n Nat) (_ : (Lte m n)) (_ : (Lte n m))) : (Eq Nat m n)
--  {[[#<zero> #<zero> <lz #<zero>> <lz #<zero>>] <refl>]
--   [[#<suc m'> #<suc n'> <ls $m' $n' $x> <ls #n' #m' $y>] (cong suc (antisym m' n' x y))]})
antisymDef :: TopExpr
antisymDef = DefCaseE "antisym" [("m", TypeE "Nat" [] []), ("n", TypeE "Nat" [] []), ("_", TypeE "Lte" [] [VarE "m", VarE "n"]), ("_", TypeE "Lte" [] [VarE "n", VarE "m"])] (TypeE "Eq" [TypeE "Nat" [] [], VarE "m"] [VarE "n"])
  [([InaccessiblePat (DataE "zero" []), InaccessiblePat (DataE "zero" []), ConsPat "lz" [InaccessiblePat (DataE "zero" [])], ConsPat "lz" [InaccessiblePat (DataE "zero" [])]], VarE "refl"),
   ([InaccessiblePat (DataE "suc" [VarE "k"]), InaccessiblePat (DataE "suc" [VarE "l"]), ConsPat"ls" [PatVar "k", PatVar "l", PatVar "x"], ConsPat "ls" [InaccessiblePat (VarE "l"), InaccessiblePat (VarE "k"), PatVar "y"]], DataE "suc" [ApplyMultiE (VarE "antisym") [VarE "k", VarE "l", VarE "x", VarE "y"]])]

--(data (Vec {(A : (Universe 0))} {(_ : Nat)}
--  {[nil  : (Vec A <zero>)]
--   [cons (n : Nat) (_ : A) (_ : (Vec A n)) : (Vec A <suc n>)]})
vecDef :: TopExpr
vecDef = DataDecE "Vec" [("A", (UniverseE 0))] [("_", TypeE "Nat" [] [])]
  [("nil", [], (TypeE "Vec" [VarE "A"] [DataE "zero" []])),
   ("cons", [("n", TypeE "Nat" [] []), ("_", VarE "A"), ("_", TypeE "Vec" [VarE "A"] [VarE "n"])], (TypeE "Vec" [VarE "A"] [DataE "suc" [VarE "n"]]))]
