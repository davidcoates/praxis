module Parse.Parse
  ( parse
  , module Parse.Parse.AST
  , module Parse.Parse.Error
  ) where

import Parse.Parse.AST
import Parse.Parse.Error
import Parse.Parse.Language

import Type
import Prelude hiding (exp)
import Text.Parsec (Parsec)
import qualified Text.Parsec as Parsec (parse)
import Control.Applicative ((<|>), (<**>), liftA2, liftA3)
import Text.Parsec.Char (string)
import Text.ParserCombinators.Parsec.Prim (many)
import Text.ParserCombinators.Parsec.Combinator (eof, many1, option, sepBy1)
import Pos
import Compile
import Control.Lens (view)

type Parser a = Parsec String () a
-- TODO Parsec Token () a


-- This is the primary function, which attempts to parse a string to an annotated sugared AST
parse :: Compiler ParseError ()
parse = do
  set stage Parse
  s <- get src
  f <- filenameDisplay
  case Parsec.parse program f s of
    Left e    -> throwError (errorPos e) e
    Right ast -> set sugaredAST (Just ast)

tag :: (Pos -> a) -> Parser a
tag = (<$> currentPos)

block :: Parser a -> Parser [a]
block p = braces (sepBy1 p semi)

program :: Parser (Annotated Exp)
program = whiteSpace *> exp <* eof

-- ^ sepBy1' is similar to sepBy1 except it includes the separator in the result
sepBy1' :: Parser a -> Parser a -> Parser [a]
sepBy1' p sep = liftA2 (:) p (concat <$> many (liftA2 join sep p))
  where join x y = [x,y]

int :: Parser (Annotated Exp)
int = tag Lit <*> (Integer <$> natural)

op :: Parser Op
op = operator

qop :: Parser Op
qop = op -- TODO: Allow qualified operators

var :: Parser String
var = identifier

qvar :: Parser String
qvar = var -- TODO: Allow qualified vars

bool :: Parser (Annotated Exp)
bool = tag Lit <*> (Bool <$> (True  <$ reserved "True" <|>
                              False <$ reserved "False" ))

lit :: Parser (Annotated Exp)
lit = bool <|> int

exp :: Parser (Annotated Exp)
exp = infixexp

infixexp :: Parser (Annotated Exp)
infixexp = tag Infix <*> (concat <$> sepBy1' lexp' (singleton (tag TOp <*> qop)))
    where lexp' :: Parser [Annotated Tok]
          lexp' = liftA2 (++) neg e
          neg = option [] (singleton (tag TNeg <* symbol "-"))
          e   = singleton (tag TExp <*> lexp)
          singleton p = (:[]) <$> p

lexp :: Parser (Annotated Exp)
lexp =  letexp <|> ifexp <|> fexp
  where ifexp = tag If
                <*> (reserved "if"   *> exp)
                <*> (reserved "then" *> exp)
                <*> (reserved "else" *> exp)
        letexp = tag Let
                 <*> (reserved "let" *> block decl)
                 <*> (reserved "in"  *> exp)

ty :: Parser Type
ty = undefined -- TODO

decl :: Parser (Annotated Decl)
decl = bang <|> decl'
  where bang = tag Bang <*> (reservedOp "!" *> var)
        decl' = do
          p <- currentPos
          v <- var
          (FunType p v <$> (reservedOp "::" >> ty)) <|> (FunDecl p v <$> (reservedOp "=" >> exp))

fexp :: Parser (Annotated Exp)
fexp = do
  xs <- many1 aexp
  return (build xs)
  where build :: [Annotated Exp] -> Annotated Exp
        build [x] = x
        build (x:y:ys) = let z = Apply (view annotation x) x y in build (z:ys)

aexp = lit <|> (tag Var <*> qvar <|> parens exp)
