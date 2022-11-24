{-# Language TypeSynonymInstances, FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, UndecidableInstances, DeriveDataTypeable,
             TypeFamilies, TupleSections, BangPatterns, TemplateHaskell, QuasiQuotes #-}

module Language.EgisonProver.Monad
       (
       -- * AST
         CheckM
       , PwlError (..)
       , MonadRuntime (..)
       , runCheckM
       , runCheckM_
       ) where

import Language.EgisonProver.AST

import Control.Exception.Safe hiding (try)
import Control.Monad.Except
import Control.Monad.Trans.State.Strict

data PwlError
  = Default String
  | TypeDoesNotMatch Expr Expr
  | UnboundVariable Name
  | ShouldBe String Expr
  | NotConvertible Expr Expr
  | Parser String

instance Show PwlError where
  show (Default msg) = "Type error: " ++ msg
  show (TypeDoesNotMatch v t) = "Type error: the type of " ++ show v ++ " does not match " ++ show t ++ "."
  show (UnboundVariable n) = "Type error: " ++ n ++ " is unbound."
  show (ShouldBe s v) = "Type error: " ++ show v ++ " should be " ++ s ++ "."
  show (NotConvertible e1 e2) = "Type error: " ++ show e1 ++ " and " ++ show e2 ++ " are not convertible."
  show (Parser msg) = "Parse error: " ++ msg

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

runCheckM_ :: CheckM a -> IO ()
runCheckM_ ma = do
  (_, _) <- runRuntimeT (runExceptT ma)
  return ()

instance MonadRuntime CheckM where
  fresh = lift fresh
  addFresh s = lift (addFresh s)
