module Parse.Parse
  ( parse
  , module Parse.Parse.AST
  ) where

import Parse.Parse.AST
import Parse.Parse.Language
import Parse.Parse.Parser

import Type
import Prelude hiding (exp)
import Control.Applicative ((<|>), (<**>), liftA2, liftA3)
import Pos
import Compile
import Control.Lens (view)


-- This is the primary function, which attempts to parse a string to an annotated sugared AST
parse :: Compiler String ()
parse = do
  set stage Parse
  ts <- get tokens
  case runParser program ts of
    Left e    -> throwError e
    Right ast -> set sugaredAST ast


program :: Parser (Annotated Exp)
program = undefined

{-
block :: Parser a -> Parser [a]
block p = braces (sepBy1 p semi)

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
-}
