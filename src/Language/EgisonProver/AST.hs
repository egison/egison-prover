{-# Language TypeSynonymInstances, FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, UndecidableInstances, DeriveDataTypeable,
             TypeFamilies, TupleSections, BangPatterns, TemplateHaskell, QuasiQuotes #-}

module Language.EgisonProver.AST
       (
       -- * AST
         TopExpr (..)
       , Expr (..)
       , Pattern (..)
       , PTopExpr (..)
       , PExpr (..)
       , PPattern (..)
       , TVal
       , Val
       , Context
       , Telescope
       , Indices
       , MName
       , Name
       , PPatternM (..)
       , pDataPat
       , pDataPatM
       , substitute
       , substitute1
       , substituteWithTelescope
       , substitutePat
       , substitutePat1
       ) where

import Control.Egison hiding (Pattern)
import qualified Control.Egison as Egison

--- Datatypes

type TVal = Expr
type Val = Expr

type Context = [(Name, TVal)]
type Telescope = [(Name, TVal)]
type Indices = [(Name, TVal)]

type MName = Maybe String
type Name = String

data TopExpr
  = DataDecE Name [(Name, Expr)] [(Name, Expr)] [(Name, [(Name, Expr)], Expr)] -- datatype name, telescope, indices, [(constructor name, args, type)]
  | DefE Name Expr Expr -- name, type, expr
  | DefFunE Name [(Name, Expr)] Expr Expr -- SHOULD DESUGARED: name, types of arguments, type of return value, expr
  | DefCaseE Name [(Name, Expr)] Expr [([Pattern], Expr)] -- SHOULD DESUGARED: name, types of arguments, type of return value, [(patterns, body)]
 deriving Show

data Expr
  = VarE Name
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
  | UndefinedE
 deriving (Show, Eq)

data Pattern
  = PatVar Name
  | DataPat Name [Pattern]
  | ValuePat Expr
 deriving (Show, Eq)

---
--- Pretty AST
---

data PTopExpr
  = PDataDecE Name [(MName, PExpr)] [(MName, PExpr)] [(Name, [(MName, PExpr)], PExpr)] -- datatype name, telescope, indices, [(constructor name, args, type)]
  | PDefE Name PExpr PExpr -- name, type, expr
  | PDefFunE Name [(MName, PExpr)] PExpr PExpr -- SHOULD DESUGARED: name, types of arguments, type of return value, expr
  | PDefCaseE Name [(MName, PExpr)] PExpr [([PPattern], PExpr)] -- SHOULD DESUGARED: name, types of arguments, type of return value, [(patterns, body)]
 deriving (Show, Eq)

data PExpr
  = PVarE Name
  | PArrowE PExpr PExpr -- SHOULD DESUGARED
  | PPiE MName PExpr PExpr
  | PLambdaE MName PExpr
  | PLambdaMultiE [MName] PExpr -- SHOULD DESUGARED
  | PApplyE PExpr PExpr
  | PApplyMultiE PExpr [PExpr] -- SHOULD DESUGARED
  | PSigmaE Name PExpr PExpr
  | PPairE PExpr PExpr
  | PProj1E PExpr
  | PProj2E PExpr
  | PUniverseE Integer
  | PUniverseAlphaE -- Only internal use: Universe for some integer alpha
  | PUnitTypeE
  | PUnitE
  | PTypeE Name [PExpr] [PExpr]
  | PDataE Name [PExpr]
  | PCaseE [(PExpr, PExpr)] [([PPattern], PExpr)]
  | PUndefinedE
 deriving (Show, Eq)

data PPattern
  = PWildcard
  | PPatVar Name
  | PDataPat Name [PPattern]
  | PValuePat PExpr
 deriving (Show, Eq)

data PPatternM = PPatternM
instance Matcher PPatternM PPattern

pDataPat :: Egison.Pattern (PP Name, PP [PPattern]) PPatternM PPattern (Name, [PPattern])
pDataPat _ _ (PDataPat n ps) = pure (n, ps)

pDataPatM :: m -> t -> (Eql, List PPatternM)
pDataPatM _ _ = (Eql, (List PPatternM))

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
substitutePat1 x v (DataPat c ps) = DataPat c (map (substitutePat1 x v) ps)
substitutePat1 x v (ValuePat e) = ValuePat (substitute1 x v e)
substitutePat1 _ _ p = p
