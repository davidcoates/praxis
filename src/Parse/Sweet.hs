{-# LANGUAGE FlexibleInstances #-}

{-
  Parse.Sweet parses sugared Praxis in to an AST. Every node of the AST is annotated with source positions.
  All sugaring is preserved in the AST, and infix expressions are not structured.
  It is up to Praxis.Unsweet to perform desugaring, and process local fixity bindings to structure infix expressions.
-}

module Parse.Sweet
  (parse, Exp(..), Lit(..), Op, Tok(..))
where

import Prelude hiding (exp)
import Control.Applicative ((<|>))
import Text.Parsec.String (Parser)
import Text.ParserCombinators.Parsec.Prim (many, getPosition)
import Text.ParserCombinators.Parsec.Combinator (eof, many1, option)
import qualified Text.ParserCombinators.Parsec.Prim as Prim (parse)
import Text.ParserCombinators.Parsec.Language (haskellStyle)
import qualified Text.ParserCombinators.Parsec.Token as Token
import Data.Tree (Tree(..))
import Data.Tree.Pretty (drawVerticalTree)
import Text.Parsec.Error (ParseError)
import AST (Tag(..), Lit(..), Annotate, Praxis, lift, tagTree)

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
identifier = Token.identifier lexer

data Exp a = If (a (Exp a)) (a (Exp a)) (a (Exp a))
           | Lit Lit
           | Fun String
           | Apply (a (Exp a)) (a (Exp a))
           | Infix [a (Tok a)]

-- Tok is used for structuring infix expressions.
-- It represents a token in an unstructure infix expression, where a token is either an expression, a binary operator, or prefix negation.
type Op = String
data Tok a = TExp (a (Exp a)) | TOp Op | TNeg

-- Pretty printing
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

-- This is the primary function, which attempts to parse a string to an annotated sugared AST
parse :: String -> Either ParseError (Praxis Exp)
parse = Prim.parse program ""

program :: Parser (Praxis Exp)
program = do { whiteSpace; e <- exp; eof; return e }

sepBy1Full :: Parser [a] -> Parser [a] -> Parser [a]
sepBy1Full a sep = do
  x <- a
  xs <- concat <$> many (do { y <- sep; z <- a; return (y ++ z) })
  return (x ++ xs)

int :: Parser (Praxis Exp)
int = lift $ (Lit . Integer) <$> natural

op :: Parser Op
op = operator

qop :: Parser Op
qop = op -- TODO: Allow qualified operators

var :: Parser String
var = identifier

qvar :: Parser String
qvar = var -- TODO: Allow qualflied vars

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
fexp = do
  xs <- many1 aexp
  return (build xs)
  where build :: [Praxis Exp] -> Praxis Exp
        build [x] = x
        build ((px :< x):(py :< y):ys) = let z = px :< Apply (px :< x) (py :< y) in build (z:ys)

aexp = lit <|> (lift (Fun <$> qvar)) <|> parens exp
