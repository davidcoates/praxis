{-# LANGUAGE FlexibleInstances #-}

module Parse.Sweet 
  (parse, Exp(..), Lit(..), Op, Tok(..))
where

import Prelude hiding (exp)
import Control.Applicative ((<|>))
import Text.Parsec.String (Parser)
import Text.ParserCombinators.Parsec.Prim (many)
import Text.ParserCombinators.Parsec.Combinator (eof, option)
import qualified Text.ParserCombinators.Parsec.Prim as Prim (parse) 
import Text.ParserCombinators.Parsec.Language (haskellStyle)
import Text.Parsec.Error (ParseError)
import qualified Text.ParserCombinators.Parsec.Token as Token

import AST (Tag(..), Lit(..), Annotate, Praxis, lift, tagTree, getPosition, SourcePos)
import Data.Tree (Tree(..))
import Data.Tree.Pretty (drawVerticalTree)

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

data Exp a = If (a (Exp a)) (a (Exp a)) (a (Exp a))
           | Lit Lit 
           | Infix [a (Tok a)]

-- Tok is used for structuring infix expressions
type Op = String
data Tok a = TExp (a (Exp a)) | TOp Op | TNeg


class TreeShow a where
  treeShow :: a -> Tree String

instance Show a => TreeShow (Annotate a Exp) where
  treeShow = tagTree treeShow'
    where treeShow' (If x y z)  = Node "[if]" [treeShow x, treeShow y, treeShow z]
          treeShow' (Lit lit)   = Node (show lit) []
          treeShow' (Infix ts)  = Node "[infix]" (map (tagTree tokShow) ts)
          tokShow TNeg     = Node "prefix[-]" []
          tokShow (TOp o)  = Node o [] 
          tokShow (TExp e) = treeShow e

instance Show a => Show (Annotate a Exp) where
  show = drawVerticalTree . treeShow


sepBy1Full :: Parser [a] -> Parser [a] -> Parser [a]
sepBy1Full a sep = do
  x <- a
  xs <- concat <$> many (do { y <- sep; z <- a; return (y ++ z) })
  return (x ++ xs)

-- instance Show (State s a) where
--   show _ = ""
-- type AExp = Exp -- (State String (), Exp)


int :: Parser (Praxis Exp)
int = lift $ (Lit . Integer) <$> natural

op :: Parser Op
op = symbol "+" <|> symbol "==" 

qop :: Parser Op
qop = op
 
lit = int

exp :: Parser (Praxis Exp)
exp = infixexp

infixexp :: Parser (Praxis Exp)
infixexp = lift $ Infix <$> sepBy1Full lexp' ((:[]) <$> lift (TOp <$> qop))
    where lexp' :: Parser [Praxis Tok]
          lexp' = do { n <- option [] (do { p <- getPosition; symbol "-"; return [p :< TNeg]}); p <- getPosition; e <- lexp; return (n ++ [p :< TExp e]) }

lexp :: Parser (Praxis Exp)
lexp =  ifexp <|> fexp
  where ifexp = lift $ do 
                { reserved "if"  ; e1 <- exp
                ; reserved "then"; e2 <- exp
                ; reserved "else"; e3 <- exp
                ; return (If e1 e2 e3) }

fexp :: Parser (Praxis Exp)
fexp = aexp

aexp = lit <|> parens exp

program :: Parser (Praxis Exp)
program = do { whiteSpace; e <- exp; eof; return e }


parse :: String -> Either ParseError (Praxis Exp)
parse = Prim.parse program ""
