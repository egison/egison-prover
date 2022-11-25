{-# Language TypeSynonymInstances, FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, UndecidableInstances, DeriveDataTypeable,
             TypeFamilies, TupleSections, BangPatterns, TemplateHaskell, QuasiQuotes #-}

module Language.EgisonProver.Desugar
       (
       -- * Desugar
         desugarTopExpr,
         desugarExpr,
         desugarPattern
       ) where

import           Language.EgisonProver.AST
import           Language.EgisonProver.Monad

desugarTopExpr :: PTopExpr -> CheckM TopExpr
desugarTopExpr (PDataDecE n as is cs) = do
  as' <- mapM (\(s, e) -> (,) <$> replaceWc s <*> desugarExpr e) as
  is' <- mapM (\(s, e) -> (,) <$> replaceWc s <*> desugarExpr e) is
  cs' <- mapM (\(s, ts, e) -> do
                  ts' <- mapM (\(s, e) -> (,) <$> replaceWc s <*> desugarExpr e) ts
                  e' <- desugarExpr e
                  return (s, ts', e')) cs
  return (DataDecE n as' is' cs')
desugarTopExpr (PDefE n t (PLambdaMultiE as e)) = do
  t' <- desugarExpr t
  as' <- mapM replaceWc as
  e' <- desugarExpr e
  return (DefE n t' (LambdaMultiE as' e'))
desugarTopExpr (PDefE n t e) = do
  t' <- desugarExpr t
  e' <- desugarExpr e
  return (DefE n t' e')
desugarTopExpr (PDefFunE n as t e) = do
  let t' = foldr (\(s, u) t' -> PPiE s u t') t as
  let e' = PLambdaMultiE (map fst as) e
  desugarTopExpr (PDefE n t' e')
desugarTopExpr (PDefCaseE n as t cs) = do
  as'   <- mapM (\(s, e) -> (, e) <$> replaceWc s) as
  let as'' = map (\(s, e) -> (Just s, e)) as'
  desugarTopExpr (PDefFunE n as'' t (PCaseE (map (\(s, e) -> (PVarE s, e)) as') cs))
  
desugarExpr :: PExpr -> CheckM Expr
desugarExpr (PVarE s) = return (VarE s)
desugarExpr (PArrowE t1 t2) = do
  s <- fresh
  desugarExpr (PPiE (Just s) t1 t2)
desugarExpr (PPiE s t1 t2) = PiE <$> replaceWc s <*> desugarExpr t1 <*> desugarExpr t2
desugarExpr (PLambdaMultiE ns e) = desugarExpr (foldr (\n e' -> PLambdaE n e') e ns)
desugarExpr (PApplyMultiE (PVarE s) as) = ApplyMultiE <$> desugarExpr (PVarE s) <*> mapM desugarExpr as
desugarExpr (PApplyMultiE f as) = desugarExpr (foldl (\f' a -> PApplyE f' a) f as)
desugarExpr (PLambdaE Nothing e1) = LambdaE <$> fresh <*> desugarExpr e1
desugarExpr (PLambdaE (Just n) e1) = LambdaE n <$> desugarExpr e1
desugarExpr (PApplyE e1 e2) = ApplyE <$> (desugarExpr e1) <*> (desugarExpr e2)
desugarExpr (PSigmaE n e1 e2) = SigmaE n <$> (desugarExpr e1) <*> (desugarExpr e2)
desugarExpr (PPairE e1 e2) = PairE <$> (desugarExpr e1) <*> (desugarExpr e2)
desugarExpr (PProj1E e1) = Proj1E <$> (desugarExpr e1)
desugarExpr (PProj2E e1) = Proj2E <$> (desugarExpr e1)
desugarExpr (PCaseE ts cs) = CaseE <$> (mapM (\(s, e) -> (,) <$> desugarExpr s <*> desugarExpr e) ts) <*> (mapM (\(ps, e) -> (,) <$> (mapM desugarPattern ps) <*> (desugarExpr e)) cs)
desugarExpr (PTypeE c ts is) = TypeE c <$> mapM desugarExpr ts <*> mapM desugarExpr is
desugarExpr (PDataE c es) = DataE c <$> mapM desugarExpr es
desugarExpr (PUniverseE n) = return (UniverseE n)
desugarExpr PUniverseAlphaE = return UniverseAlphaE
desugarExpr PUnitTypeE = return UnitTypeE
desugarExpr PUnitE = return UnitE

desugarPattern :: PPattern -> CheckM Pattern
desugarPattern PWildcard = PatVar <$> fresh
desugarPattern (PPatVar s) = return (PatVar s)
desugarPattern (PValuePat e) = ValuePat <$> desugarExpr e
desugarPattern (PDataPat n ps) = DataPat n <$> mapM desugarPattern ps

replaceWc :: MName -> CheckM Name
replaceWc Nothing = fresh
replaceWc (Just s) = return s
