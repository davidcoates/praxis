module Parse.Sweet 
  (parse, Expr(..), Lit(..), Op(..))
where

import Prelude hiding (exp)
import Control.Applicative ((<|>))
import Text.Parsec (State, parseTest, try)
import Text.Parsec.String (Parser)
import Text.ParserCombinators.Parsec.Char (digit)
import Text.ParserCombinators.Parsec.Combinator (many1, eof, sepBy1)
import Text.ParserCombinators.Parsec.Prim (many)
import qualified Text.ParserCombinators.Parsec.Prim as Prim (parse) 
import Text.ParserCombinators.Parsec.Language (haskellDef)
import Text.Parsec.Error (ParseError)
import qualified Text.ParserCombinators.Parsec.Token as Token

lexer = Token.makeTokenParser haskellDef
lexeme     = Token.lexeme     lexer
whiteSpace = Token.whiteSpace lexer
operator   = Token.operator   lexer
symbol     = Token.symbol     lexer
parens     = Token.parens     lexer
integer    = Token.integer    lexer

data Lit = Integer Integer
         deriving (Show)

data Op = Plus | Eq
        deriving (Show)

-- data Binding = Binding String Expr
--             deriving (Show)

data Expr = Lit Lit
--          | Let [Binding] Expr
--          | If Expr Expr Expr
          | OpSequence [Expr] [Op]
          deriving (Show)

sepBy1Full :: Parser a -> Parser sep -> Parser ([a], [sep])
sepBy1Full a sep = do
  x <- a
  (os, xs) <- unzip <$> many (do { y <- sep; z <- a; return (y, z) })
  return (x:xs, os)

-- instance Show (State s a) where
--   show _ = ""
-- type AExpr = Expr -- (State String (), Expr)

int :: Parser Expr
int = (Lit . Integer) <$> integer

op :: Parser Op
op = do { s <- symbol "+"; return Plus } <|> do { s <- symbol "=="; return Eq }
 
qop :: Parser Op
qop = op
 
lit = int

exp :: Parser Expr
exp = infixexp

infixexp :: Parser Expr
infixexp = do
  (es, os) <- sepBy1Full lexp qop
  return (OpSequence es os)

lexp :: Parser Expr
lexp = fexp
-- <|> let ... in ....

fexp :: Parser Expr
fexp = aexp

aexp = lit <|> parens exp

program :: Parser Expr
program = exp

parse :: String -> Either ParseError Expr
parse = Prim.parse program ""

