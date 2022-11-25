{-# Language TypeSynonymInstances, FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, UndecidableInstances, DeriveDataTypeable,
             TypeFamilies, TupleSections, BangPatterns, TemplateHaskell, QuasiQuotes #-}


module Main where

import System.Environment (getArgs)

import Control.Exception.Safe hiding (try)
import Control.Monad.Except
import Control.Monad.Trans.State.Strict

import Language.EgisonProver

main :: IO ()
main = do
  [file] <- getArgs
  liftIO (putStrLn ("file: " ++ file))
  ret <- runCheckM (do
    topExprs <- loadFile file
    liftIO (putStrLn ("topExprs: " ++ show topExprs))
    topExprs' <- mapM desugarTopExpr topExprs
    let envV = initTopVEnv topExprs'
    let envT = initTopTEnv topExprs'
    let envD = initTopDEnv topExprs'
    let envC = initTopCEnv topExprs'
    let env = (envV, envT, envD, envC)
    mapM_ (\e -> do
             liftIO (putStrLn ("input: " ++ show e))
             e' <- checkTopExpr env e
             liftIO (putStrLn ("output: " ++ show e'))) topExprs')
  liftIO (putStrLn ("ret: " ++ show ret))
