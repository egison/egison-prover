{-# Language TypeSynonymInstances, FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, UndecidableInstances, DeriveDataTypeable,
             TypeFamilies, TupleSections, BangPatterns, TemplateHaskell, QuasiQuotes #-}

module Language.EgisonProver.Parser
       (
       -- * Parse
         readTopExprs
       , readTopExpr
       -- * Load files
       , loadFile
       ) where

import           Language.EgisonProver.AST
import           Language.EgisonProver.Monad

import           Text.Parsec
import           Text.Parsec.String
import qualified Text.Parsec.Token      as P
import           Control.Monad.Identity (Identity)

import           System.Directory             (doesFileExist, getHomeDirectory)
import           System.IO

import Control.Exception.Safe hiding (try)
import Control.Monad.Except
import Control.Monad.Trans.State.Strict

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
  s <- char '$' >> ident
  whiteSpace
  ts <- braces (sepEndBy mNameWithType whiteSpace)
  is <- braces (sepEndBy mNameWithType whiteSpace)
  cs <- braces (sepEndBy consDec whiteSpace)
  return (PDataDecE s ts is cs))

consDec :: Parser (Name, [(MName, PExpr)], PExpr)
consDec = brackets (do
  c <- char '$' >> ident
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
      s <- char '$' >> ident
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
      s <- char '$' >> ident
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
  char '→' >> whiteSpace
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
  char 'λ' >> whiteSpace
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
  s <- char '$' >> ident
  whiteSpace >> char ':' >> whiteSpace
  t <- expr
  return (s, t))

mNameWithType :: Parser (MName, PExpr)
mNameWithType = parens (do
  s <- (try (char '_' >> return Nothing) <|> try (char '$' >> ident >>= return . Just))
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

