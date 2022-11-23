{-# Language TypeSynonymInstances, FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, UndecidableInstances, DeriveDataTypeable,
             TypeFamilies, TupleSections, BangPatterns, TemplateHaskell, QuasiQuotes #-}


module Main where

import           Text.Parsec
import           Text.Parsec.String
import qualified Text.Parsec.Token      as P
import           Control.Monad.Identity (Identity)

import           System.Directory             (doesFileExist, getHomeDirectory)
import           System.IO
import           System.Environment           (getArgs)

import Control.Exception.Safe hiding (try)
import Control.Monad.Except
import Control.Monad.Trans.State.Strict
import Control.Egison hiding (Pattern)
import qualified Control.Egison as Egison

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
    liftIO (putStrLn ("test"))
    mapM_ (\e -> do
             liftIO (putStrLn ("input: " ++ show e))
             e' <- desugarTopExpr e >>= checkTopExpr env
             liftIO (putStrLn ("output: " ++ show e'))) [plusZeroDef]
    mapM_ (\e -> do
             liftIO (putStrLn ("input: " ++ show e))
             e' <- checkTopExpr env e
             liftIO (putStrLn ("output: " ++ show e'))) topExprs')
  liftIO (putStrLn ("ret: " ++ show ret))

--- Monad

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
  
--- Datatypes

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
 deriving Show

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

---
--- Parser
---

loadFile :: FilePath -> CheckM [PTopExpr]
loadFile file = do
  doesExist <- liftIO $ doesFileExist file
  unless doesExist $ throwError $ Default ("file does not exist: " ++ file)
  input <- liftIO $ readUTF8File file
  readTopExprs (removeShebang input)

removeShebang :: String -> String
removeShebang cs@('#':'!':_) = ';' : cs
removeShebang cs             = cs

readUTF8File :: FilePath -> IO String
readUTF8File name = do
  h <- openFile name ReadMode
  hSetEncoding h utf8
  hGetContents h

readTopExprs :: String -> CheckM [PTopExpr]
readTopExprs input = do
  either (throwError . Parser) return (parseTopExprs input)

readTopExpr :: String -> CheckM PTopExpr
readTopExpr input = do
  either (throwError . Parser) return (parseTopExpr input)

parseTopExprs :: String -> Either String [PTopExpr]
parseTopExprs = doParse $ do
  ret <- whiteSpace >> endBy topExpr whiteSpace
  eof
  return ret

parseTopExpr :: String -> Either String PTopExpr
parseTopExpr = doParse $ do
  ret <- whiteSpace >> topExpr
  whiteSpace >> eof
  return ret

doParse :: Parser a -> String -> Either String a
doParse p input = either (throwError . show) return $ parse p "egison-prover" input


whiteSpace :: Parser ()
whiteSpace = P.whiteSpace lexer

parens :: Parser a -> Parser a
parens = P.parens lexer

brackets :: Parser a -> Parser a
brackets = P.brackets lexer

braces :: Parser a -> Parser a
braces = P.braces lexer

angles :: Parser a -> Parser a
angles = P.angles lexer

ident :: Parser String
ident = P.identifier lexer

topExpr :: Parser PTopExpr
topExpr = try dataDecExpr
      <|> try defCaseExpr
      <|> try defFunExpr
      <|> try defExpr
      <?> "top-level expression"

dataDecExpr :: Parser PTopExpr
dataDecExpr = parens (do
  keywordData
  s <- ident
  whiteSpace
  ts <- braces (sepEndBy mNameWithType whiteSpace)
  is <- braces (sepEndBy mNameWithType whiteSpace)
  cs <- braces (sepEndBy consDec whiteSpace)
  return (PDataDecE s ts is cs))

consDec :: Parser (Name, [(MName, PExpr)], PExpr)
consDec = brackets (do
  c <- ident
  whiteSpace
  as <- sepEndBy mNameWithType whiteSpace
  char ':' >> whiteSpace
  t <- expr
  return (c, as, t))

defExpr :: Parser PTopExpr
defExpr = parens (do
  keywordDefine
  (s, t) <- nameWithType
  whiteSpace
  b <- expr
  return (PDefE s t b))

defFunExpr :: Parser PTopExpr
defFunExpr = parens (do
  keywordDefine
  (s, as, t) <- parens (do
    (s, as) <- parens (do
      s <- ident
      whiteSpace
      as <- sepEndBy mNameWithType whiteSpace
      return (s, as))
    char ':' >> whiteSpace
    t <- expr
    return (s, as, t))
  b <- expr
  return (PDefFunE s as t b))

defCaseExpr :: Parser PTopExpr
defCaseExpr = parens (do
  keywordDefine
  (s, as, t) <- parens (do
    (s, as) <- parens (do
      s <- ident
      whiteSpace
      as <- sepEndBy mNameWithType whiteSpace
      return (s, as))
    char ':' >> whiteSpace
    t <- expr
    return (s, as, t))
  mcs <- braces (sepEndBy matchClause whiteSpace)
  return (PDefCaseE s as t mcs))

matchClause :: Parser ([PPattern], PExpr)
matchClause = brackets (do
  ps <- brackets (sepEndBy pat whiteSpace)
  b <- expr
  return (ps, b))

expr :: Parser PExpr
expr = try arrowExpr
   <|> try expr'

expr' :: Parser PExpr
expr' = try varExpr
    <|> try dataExpr
    <|> try typeExpr
    <|> try universeExpr
    <|> try lambdaExpr
    <|> try piExpr
    <|> try applyExpr

arrowExpr :: Parser PExpr
arrowExpr = do
  e1 <- expr'
  string "->" >> whiteSpace
  e2 <- expr'
  return (PArrowE e1 e2)

varExpr :: Parser PExpr
varExpr = do
  s <- ident
  return (PVarE s)

dataExpr :: Parser PExpr
dataExpr = angles (do
  s <- (:) <$> lower <*> ident
  whiteSpace
  args <- sepEndBy expr whiteSpace
  return (PDataE s args))

typeExpr :: Parser PExpr
typeExpr = angles (do
  s <- (:) <$> upper <*> ident
  whiteSpace
  ts <- braces (sepEndBy expr whiteSpace)
  is <- braces (sepEndBy expr whiteSpace)
  return (PTypeE s ts is))

universeExpr :: Parser PExpr
universeExpr = parens (do
  keywordUniverse
  whiteSpace
  n <- P.natural lexer
  return (PUniverseE n))

lambdaExpr :: Parser PExpr
lambdaExpr = parens (do
  keywordLambda
  whiteSpace
  as <- brackets (sepEndBy (char '$' >> Just <$> ident) whiteSpace)
  b <- expr
  return (PLambdaMultiE as b))

piExpr :: Parser PExpr
piExpr = parens (do
  char 'Π'
  whiteSpace
  (n, t) <- mNameWithType
  b <- expr
  return (PPiE n t b))

applyExpr :: Parser PExpr
applyExpr = parens (do
  f <- expr
  whiteSpace
  as <- sepEndBy expr whiteSpace
  return (PApplyMultiE f as))

pat :: Parser PPattern
pat = try (char '_' >> return PWildcard)
  <|> try (char '$' >> ident >>= return . PPatVar)
  <|> try (char '#' >> expr >>= return . PValuePat)
  <|> try (angles (do c <- ident
                      whiteSpace
                      args <- sepEndBy pat whiteSpace
                      return (PDataPat c args)))

nameWithType :: Parser (Name, PExpr)
nameWithType = parens (do
  s <- ident
  whiteSpace >> char ':' >> whiteSpace
  t <- expr
  return (s, t))

mNameWithType :: Parser (MName, PExpr)
mNameWithType = parens (do
  s <- (try (char '_' >> return Nothing) <|> try (Just <$> ident))
  whiteSpace >> char ':' >> whiteSpace
  t <- expr
  return (s, t))

egisonDef :: P.GenLanguageDef String () Identity
egisonDef =
  P.LanguageDef { P.commentStart       = "#|"
                , P.commentEnd         = "|#"
                , P.commentLine        = ";"
                , P.identStart         = letter <|> symbol1 <|> symbol0
                , P.identLetter        = letter <|> digit <|> symbol2
                , P.opStart            = symbol1
                , P.opLetter           = symbol1
                , P.reservedNames      = reservedKeywords
                , P.reservedOpNames    = reservedOperators
                , P.nestedComments     = True
                , P.caseSensitive      = True }

symbol0 = char '^'
-- Don't allow three consecutive dots to be a part of identifier
symbol1 = oneOf "+-*/=∂∇" <|> try (char '.' <* notFollowedBy (string ".."))
symbol2 = symbol1 <|> oneOf "'!?₀₁₂₃₄₅₆₇₈₉"

lexer :: P.GenTokenParser String () Identity
lexer = P.makeTokenParser egisonDef

reservedKeywords :: [String]
reservedKeywords =
  [ "data"
  , "define"
  , "case"
  , "lambda"
  , "Universe"
  , "undefined"]

reservedOperators :: [String]
reservedOperators =
  [ ":"
  , "$"
  , "_"
  , "->"
  , "..."]

reserved :: String -> Parser ()
reserved = P.reserved lexer

reservedOp :: String -> Parser ()
reservedOp = P.reservedOp lexer

keywordData                 = reserved "data"
keywordDefine               = reserved "define"
keywordUniverse             = reserved "Universe"
keywordLambda               = reserved "lambda"

---
--- Environment
---

data PatternM = PatternM
instance Matcher PatternM Pattern

--dataPat :: Egison.Pattern (PP Name, PP [Pattern]) PatternM Pattern (Name, [Pattern])
--dataPat _ _ (DataPat n ps) = pure (n, ps)

--dataPatM :: m -> t -> (Something, List PatternM)
--dataPatM _ _ = (Something, (List PatternM))

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
--  checkCoverage env (map snd ts) (map fst mcs)
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
substituteWithTelescope _ _ _ = throw (Default "substituteWithTelescope: should not reach here")

substitutePat :: [(Name, Expr)] -> Pattern -> Pattern
substitutePat [] p = p
substitutePat ((x, v) : ms) p = substitutePat ms (substitutePat1 x v p)

substitutePat1 :: Name -> Expr -> Pattern -> Pattern
substitutePat1 x v (DataPat c ps) = DataPat c (map (substitutePat1 x v) ps)
substitutePat1 x v (ValuePat e) = ValuePat (substitute1 x v e)
substitutePat1 _ _ p = p

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
      (qs', ret', us', vs') <- checkPattern' env' xts' qs [] ret us vs
      let b' = (substitute ((zip (map fst tts) ats') ++ (zip (map fst xts) (map fst xts'))) b)
      case b' of
        TypeE _ bts bis -> do
          _ <- checkTelescope env bts tts
          checkPattern' env cs ps (pat ++ [DataPat c qs']) ret' (us' ++ [(e, DataE c (map fst xts'))] ++ zip ais bis) vs'
        _ -> throwError (Default "")
    _ -> throwError (Default "")
checkPattern' _ _ _ _ _ _ _ = throwError (Default "checkPattern': should not reach here")

unify :: [(Expr, Expr)] -> CheckM [(Name, Expr)]
unify [] = return []
unify ((x@(VarE _), y) : _) | x == y = throwError (Default ("unify deletion rule: " ++ show (x, y)))
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

checkCoverage :: Env -> [TVal] -> [[Pattern]] -> CheckM ()
checkCoverage env ts pss = undefined -- checkCoverage' env [(map (\_ -> Wildcard) ts)] ts pss

checkCoverage' :: Env -> [[Pattern]] -> [TVal] -> [[Pattern]] -> CheckM ()
checkCoverage' _ [] _ _ = return ()
checkCoverage' env (qs : qss) ts (ps : pss) = do
  b1 <- matchPattern qs ps
  if b1
    then do
      nss <- getNeighbors env ts ps
      checkCoverage' env nss ts pss
    else do
      b2 <- isAbsurd ts qs
      if b2
        then checkCoverage' env qss ts (ps : pss)
        else throwError (Default "checkCoverage': patterns are not exhaustive")
checkCoverage' _ _ _ _ = throwError (Default "checkCoverage': should not reach here")

matchPattern :: [Pattern] -> [Pattern] -> CheckM Bool
matchPattern [] [] = return True
matchPattern (q : qs) (p : ps) = (&&) <$> matchPattern1 q p <*> matchPattern qs ps

matchPattern1 :: Pattern -> Pattern -> CheckM Bool
matchPattern1 (DataPat c1 qs) (DataPat c2 ps) =
  if c1 == c2
    then matchPattern qs ps
    else return False
matchPattern1 q p = return (q == p)
           
isAbsurd :: [TVal] -> [Pattern] -> CheckM Bool
isAbsurd _ _ = return True
           
getNeighbors :: Env -> [TVal] -> [Pattern] -> CheckM [[Pattern]]
getNeighbors = undefined
