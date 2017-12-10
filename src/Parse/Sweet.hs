module Parse.Sweet 
  (parse, Expr(..), Lit(..), Op(..), Tok(..))
where

import Prelude hiding (exp)
import Control.Applicative ((<|>))
import Text.Parsec (State, parseTest, try)
import Text.Parsec.String (Parser)
import Text.ParserCombinators.Parsec.Char (digit)
import Text.ParserCombinators.Parsec.Prim (many)
import Text.ParserCombinators.Parsec.Combinator
import qualified Text.ParserCombinators.Parsec.Prim as Prim (parse) 
import Text.ParserCombinators.Parsec.Language (haskellStyle)
import Text.Parsec.Error (ParseError)
import qualified Text.ParserCombinators.Parsec.Token as Token

praxisDef =
  haskellStyle
    { Token.reservedNames   = ["if", "then", "else"]
    , Token.reservedOpNames = ["=", "\\", "->", "=>", "@", "?", ":", "::"]
    }

lexer = Token.makeTokenParser praxisDef

lexeme     = Token.lexeme     lexer
whiteSpace = Token.whiteSpace lexer
operator   = Token.operator   lexer
symbol     = Token.symbol     lexer
parens     = Token.parens     lexer
integer    = Token.integer    lexer
natural    = Token.natural    lexer
reserved   = Token.reserved   lexer

data Lit = Integer Integer
         deriving (Show)

data Op = Op String
        deriving (Show, Ord, Eq)

-- data Binding = Binding String Expr
--             deriving (Show)

data Tok = TExp Expr | TOp Op | TNeg
         deriving (Show)

data Expr = Lit Lit
--          | Let [Binding] Expr
          | If Expr Expr Expr
          | OpSequence [Tok]
          deriving (Show)

sepBy1Full :: Parser [a] -> Parser [a] -> Parser [a]
sepBy1Full a sep = do
  x <- a
  xs <- concat <$> many (do { y <- sep; z <- a; return (y ++ z) })
  return (x ++ xs)

-- instance Show (State s a) where
--   show _ = ""
-- type AExpr = Expr -- (State String (), Expr)

int :: Parser Expr
int = (Lit . Integer) <$> natural

op :: Parser Op
op = ( Op <$> symbol "+" ) <|> ( Op <$> symbol "==" )
 
qop :: Parser Op
qop = op
 
lit = int

exp :: Parser Expr
exp = infixexp

infixexp :: Parser Expr
infixexp = OpSequence <$> sepBy1Full lexp' ((\x -> [TOp x]) <$> qop)
    where lexp' :: Parser [Tok]
          lexp' = do { n <- option [] (symbol "-" >> return [TNeg]); e <- lexp; return (n ++ [TExp e]) }

lexp :: Parser Expr
lexp =  ifexp <|> fexp
  where ifexp = do 
                { reserved "if"  ; e1 <- exp
                ; reserved "then"; e2 <- exp
                ; reserved "else"; e3 <- exp
                ; return (If e1 e2 e3) }

fexp :: Parser Expr
fexp = aexp

aexp = lit <|> parens exp

program :: Parser Expr
program = do { whiteSpace; e <- exp; eof; return e }

parse :: String -> Either ParseError Expr
parse = Prim.parse program ""

