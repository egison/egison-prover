{-# Language TypeSynonymInstances, FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, UndecidableInstances, DeriveDataTypeable,
             TypeFamilies, TupleSections, BangPatterns, TemplateHaskell, QuasiQuotes #-}


module Main where

import Control.Exception.Safe
import Control.Monad.Except
import Control.Egison hiding (Pattern)

main :: IO ()
main = do
  ret <- runCheckM (checkTopExpr [] (desugarTopExpr idDef))
  case ret of
    Left err -> print err
    Right expr -> print (show expr)
  ret <- runCheckM (checkTopExpr [] (desugarTopExpr compDef))
  case ret of
    Left err -> print err
    Right expr -> print (show expr)
  
---
--- Monad
---

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

---
--- Datatypes
---

type Name = String

data TopExpr
  = DataDecE Name [(Name, Expr)] Expr [(Name, Expr)] -- datatype name, telescope, type, [(constructor name, type)]
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
  | TypeE Expr [Expr]
  | DataE Name [Expr]
  | CaseE [Expr] [([Pattern], Expr)]
 deriving Show

data Pattern
  = PatVar Name
  | Pattern Name [Pattern]
  | InaccessiblePat Expr
 deriving Show

type TVal = Expr
type Val = Expr

type TEnv = [(Name, TVal)]
type VEnv = [(Name, Val)]
  
type Context = [(Name, Expr)]
type Telescope = [(Name, Expr)]

getFromTEnv :: TEnv -> Name -> CheckM TVal
getFromTEnv gamma x =
  match dfs gamma (List (Pair Eql Something))
    [[mc| _ ++ (#x, $t) : _ -> return t |],
     [mc| _ -> throw (UnboundVariable x) |]]

---
--- Desugar
---

desugarTopExpr :: TopExpr -> TopExpr
desugarTopExpr (DataDecE n as t cs) =
  let as' = map (\(s, e) -> (s, desugarExpr e)) as
      t' = desugarExpr t
      cs' = map (\(s, e) -> (s, desugarExpr e)) cs
  in DataDecE n as' t' cs'
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
desugarPattern (Pattern n ps) = Pattern n (map desugarPattern ps)
desugarPattern p = p
                
---
--- Type checking
---

checkTopExpr :: TEnv -> TopExpr -> CheckM TopExpr
checkTopExpr gamma (DefE n t e) = do
  e' <- check gamma e t
  return (DefE n t e')

check :: TEnv -> Expr -> Expr -> CheckM Expr
check gamma (LambdaE x e) a = do
  a' <- evalWHNF a
  case a' of
    PiE y b c -> do
      e' <- check (gamma ++ [(x, b)]) e c
      return (LambdaE x e')
    _ -> throw (TypeDoesNotMatch (LambdaE x e) a')
check gamma (PairE e1 e2) a = do
  a' <- evalWHNF a
  case a' of
    SigmaE x b c -> do
      s <- check gamma e1 b
      t <- check gamma e2 (substitute x s c)
      return (PairE s t)
    _ -> throw (TypeDoesNotMatch (PairE e1 e2) a')
check gamma e a = do
  (b, t) <- infer gamma e
  isSubtype gamma a b
  return t

infer :: TEnv -> Expr -> CheckM (Expr, Expr)
infer gamma e@(VarE x) = do
  a <- getFromTEnv gamma x
  return (a, e)
infer gamma (ApplyE e1 e2) = do
  (a, s) <- infer gamma e1
  a' <- evalWHNF a
  case a' of
    PiE x b c -> do
      t <- check gamma e2 b
      return (substitute x t c, ApplyE s t)
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
      return (substitute x (Proj1E t) c, Proj2E t)
    _ -> throw (ShouldBe "pair" e)
infer gamma (PiE x e1 e2) = do
  (c1, a) <- infer gamma e1
  (c2, b) <- infer (gamma ++ [(x, a)]) e2
  c1' <- evalWHNF c1
  c2' <- evalWHNF c2
  case (c1', c2') of
    (UniverseE i, UniverseE j) -> do
      return (UniverseE (max i j), PiE x a b)
    _ -> throw (Default "")
infer gamma (SigmaE x e1 e2) = do
  (c1, a) <- infer gamma e1
  (c2, b) <- infer (gamma ++ [(x, a)]) e2
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
infer _ _ = throw (Default "not implemented")

isSubtype :: TEnv -> Expr -> Expr -> CheckM ()
isSubtype gamma a b = do
  a' <- evalWHNF a
  b' <- evalWHNF b
  isSubtype' gamma a' b'

isSubtype' :: TEnv -> Expr -> Expr -> CheckM ()
isSubtype' _ (UniverseE i) (UniverseE j) =
  if i + 1 == j then return () else throw (Default "")
isSubtype' gamma (PiE x a1 b1) (PiE y a2 b2) =
  if x == y
    then do
      isConvertible gamma a1 a2 UniverseAlphaE
      isSubtype (gamma ++ [(x, a1)]) b1 b2
    else throw (NotConvertible (PiE x a1 b1) (PiE y a2 b2))
isSubtype' gamma (SigmaE x a1 b1) (SigmaE y a2 b2) =
  if x == y
    then do
      isConvertible gamma a1 a2 UniverseAlphaE
      isSubtype (gamma ++ [(x, a1)]) b1 b2
    else throw (NotConvertible (SigmaE x a1 b1) (SigmaE y a2 b2))
isSubtype' gamma a b = isConvertible' gamma a b UniverseAlphaE

isConvertible :: TEnv -> Expr -> Expr -> Expr -> CheckM ()
isConvertible gamma s t a = do
  s' <- evalWHNF s
  t' <- evalWHNF t
  a' <- evalWHNF a
  isConvertible' gamma s' t' a'

isConvertible' :: TEnv -> Expr -> Expr -> Expr -> CheckM ()
isConvertible' gamma (UniverseE i) (UniverseE j) UniverseAlphaE =
  if i == j then return () else throw (NotConvertible (UniverseE i) (UniverseE j))
isConvertible' gamma (PiE x a1 b1) (PiE y a2 b2) UniverseAlphaE =
  if x == y
    then do
      isConvertible gamma a1 a2 UniverseAlphaE
      isConvertible (gamma ++ [(x, a1)]) b1 b2 UniverseAlphaE
    else throw (NotConvertible (PiE x a1 b1) (PiE y a2 b2))
isConvertible' gamma (SigmaE x a1 b1) (SigmaE y a2 b2) UniverseAlphaE =
  if x == y
    then do
      isConvertible gamma a1 a2 UniverseAlphaE
      isConvertible (gamma ++ [(x, a1)]) b1 b2 UniverseAlphaE
    else throw (NotConvertible (SigmaE x a1 b1) (SigmaE y a2 b2))
isConvertible' gamma s t UnitTypeE = return ()
isConvertible' gamma s t (PiE x a b) = isConvertible (gamma ++ [(x, a)]) (ApplyE s (VarE x)) (ApplyE t (VarE x)) b
isConvertible' gamma s t (SigmaE x a b) = do
  isConvertible gamma (Proj1E s) (Proj1E t) a
  isConvertible gamma (Proj2E s) (Proj2E t) (substitute x (Proj1E s) b)
isConvertible' gamma s t a = do
  if isNeutral s && isNeutral t
    then do
      _ <- isEqual gamma s t
      return ()
    else throw (Default "")

isEqual :: TEnv -> Expr -> Expr -> CheckM Expr
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
      return (substitute x t1 c)
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
      return (substitute x (Proj1E s) c)
    _ -> throw (Default "")

---
--- Utility functions
---

evalWHNF :: Expr -> CheckM Expr
evalWHNF (ApplyE e1 e2) = do
  e1' <- evalWHNF e1
  case e1' of
    LambdaE x b -> return (substitute x e2 b) 
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

substitute :: Name -> Expr -> Expr -> Expr
substitute x v e@(VarE y) | x == y    = v
                          | otherwise = e
substitute x v e@(PiE y e1 e2) | x == y    = e
                               | otherwise = PiE y (substitute x v e1) (substitute x v e2)
substitute x v e@(LambdaE y e1) | x == y    = e
                                | otherwise = LambdaE y (substitute x v e1)
substitute x v (ApplyE e1 e2) = ApplyE (substitute x v e1) (substitute x v e2)
substitute x v e@(SigmaE y e1 e2) | x == y    = e
                                  | otherwise = SigmaE y (substitute x v e1) (substitute x v e2)
substitute x v (PairE e1 e2) = PairE (substitute x v e1) (substitute x v e2)
substitute x v (Proj1E e1) = Proj1E (substitute x v e1)
substitute x v (Proj2E e1) = Proj2E (substitute x v e1)
substitute _ _ e = e

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

--(data Nat : (Universe 0)
--  {[zero : Nat]
--   [suc (_ : Nat) : Nat]})
natDef :: TopExpr
natDef = DataDecE "Nat" [] (UniverseE 0)
  [("zero", (VarE "Nat")),
   ("suc", (ArrowE (VarE "Nat") (VarE "Nat")))]

--(data (Eq (A : (Universe 0)) (x : A)) : A -> (Universe 0)
--  {[refl  : (Eq A x x)]})
eqDef :: TopExpr
eqDef = DataDecE "Eq" [("A", UniverseE 0), ("x", VarE "A")] (ArrowE (VarE "A") (UniverseE 0))
  [("refl", TypeE (VarE "Eq") [VarE "A", VarE "x", VarE "x"])]

--(def (cong (f : A -> B) (x : A) (y : A) (_ : (Eq x y))) : (Eq (f x) (f y))
--  {[[_ _ _ <refl>] <refl>]})
congDef :: TopExpr
congDef = DefCaseE "cong" [("f", ArrowE (VarE "A") (VarE "B")), ("x", VarE "A"), ("y", VarE "A"), ("_", TypeE (VarE "Eq") [VarE "x", VarE "y"])] (TypeE (VarE "Eq") [ApplyE (VarE "f") (VarE "x"), ApplyE (VarE "f") (VarE "y")])
  [([PatVar "f", Pattern "refl" []], VarE "refl")]

--(define (plus (_ : Nat) (_ : Nat)) : Nat
--  {[[<zero> $n] n]
--   [[<suc $m> $n] <suc (plus m n)>]})
plusDef :: TopExpr
plusDef = DefCaseE "plus" [("_", VarE "Nat"), ("_", VarE "Nat")] (VarE "Nat")
  [([Pattern "zero" [], PatVar "n"], VarE "n"),
   ([Pattern "suc" [(PatVar "m")], PatVar "n"], DataE "suc" [ApplyMultiE (VarE "plus") [VarE "m", VarE "n"]])]

--(def (plusZero (n : Nat)) : (Eq (plus n <zero>) n)
--  {[<zero> <refl>]
--   [<suc $m> (cong suc (plusZero m))]})
plusZeroDef :: TopExpr
plusZeroDef = DefCaseE "plusZero" [("n", VarE "Nat")] (TypeE (VarE "Eq") [ApplyMultiE (VarE "plus") [(VarE "n"), (VarE "zero")], (VarE "n")])
  [([Pattern "zero" []], VarE "refl"),
   ([Pattern "suc" [PatVar "m"]], ApplyMultiE (VarE "cong") [VarE "suc", ApplyE (VarE "plusZero") (VarE "m")])]

--(data Lte : Nat -> Nat -> (Universe 0)
--  {[lz (y : Nat) : (Lte <zero> y)]
--   [ls (x : Nat) (y : Nat) (_ : (Lte x y)) : (Lte <suc x> <suc y>)]})
lteDef :: TopExpr
lteDef = DataDecE "Lte" [] (ArrowE (VarE "Nat") (ArrowE (VarE "Nat") (UniverseE 0)))
  [("lz", PiE "n" (VarE "Nat") (TypeE (VarE "Lte") [VarE "zero", VarE "n"])),
   ("ls", PiE "m" (VarE "Nat") (PiE "n" (VarE "Nat") (ArrowE (TypeE (VarE "Lte") [VarE "m", VarE "n"]) (TypeE (VarE "Lte") [DataE "suc" [VarE "m"], DataE "suc" [VarE "n"]]))))]

--(def (antisym (m : Nat) (n Nat) (_ : (Lte m n)) (_ : (Lte n m))) : (Eq m n)
--  {[[#<zero> #<zero> <lz #<zero>> <lz #<zero>>] <refl>]
--   [[#<suc m'> #<suc n'> <ls $m' $n' $x> <ls #n' #m' $y>] (cong suc (antisym m' n' x y))]})
antisymDef :: TopExpr
antisymDef = DefCaseE "antisym" [("m", VarE "Nat"), ("n", VarE "Nat"), ("_", TypeE (VarE "Lte") [VarE "m", VarE "n"]), ("_", TypeE (VarE "Lte") [VarE "n", VarE "m"])] (TypeE (VarE "Eq") [VarE "m", VarE "n"])
  [([InaccessiblePat (DataE "zero" []), InaccessiblePat (DataE "zero" []), Pattern "lz" [InaccessiblePat (DataE "zero" [])], Pattern "lz" [InaccessiblePat (DataE "zero" [])]], VarE "refl"),
   ([InaccessiblePat (DataE "suc" [VarE "k"]), InaccessiblePat (DataE "suc" [VarE "l"]), Pattern"ls" [PatVar "k", PatVar "l", PatVar "x"], Pattern "ls" [InaccessiblePat (VarE "l"), InaccessiblePat (VarE "k"), PatVar "y"]], DataE "suc" [ApplyMultiE (VarE "antisym") [VarE "k", VarE "l", VarE "x", VarE "y"]])]

--(data (Vec (A : (Universe 0)) (_ : Nat)) : (Universe 0)
--  {[nil  : (Vec A <zero>)]
--   [cons (n : Nat) (_ : A) (_ : (Vec A n)) : (Vec A <suc n>)]})
vecDef :: TopExpr
vecDef = DataDecE "Vec" [("A", (UniverseE 0))] (ArrowE (VarE "Nat") (UniverseE 0))
  [("nil", (TypeE (VarE "Vec") [(VarE "A"), (VarE "zero")])),
   ("cons", (PiE "n" (VarE "Nat") (ArrowE (VarE "A") (ArrowE (TypeE (VarE "Vec") [(VarE "A"), (VarE "n")]) (TypeE (VarE "Vec") [(VarE "A"), (DataE "suc" [VarE "n"])])))))]
