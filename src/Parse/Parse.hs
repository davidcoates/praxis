module Parse.Parse
  ( parse
  -- , module Parse.Parse.AST
  ) where

import Parse.Parse.AST as Parse
import Parse.Tokenise.Token as Token
import Parse.Parse.Parser

import Type
import Tag
import Source
import Compiler

import Prelude hiding (exp)
import Control.Applicative ((<|>), (<**>), liftA2, liftA3, empty)
import Control.Lens (view)
import Data.Maybe (isJust, fromJust)

type T a = a (Tag Source)

-- TODO move these to Parse/Parser?
optional :: Parser a -> Parser ()
optional p = p *> pure () <|> pure ()

liftT2 :: (a -> b -> c) -> Parser a -> Parser b -> Parser c
liftT2 f a b = liftA2 f a (optional whitespace *> b)

liftT3 :: (a -> b -> c -> d) -> Parser a -> Parser b -> Parser c -> Parser d
liftT3 f a b c = liftT2 f a b <*> (optional whitespace *> c)

liftT4 :: (a -> b -> c -> d -> e) -> Parser a -> Parser b -> Parser c -> Parser d -> Parser e
liftT4 f a b c d = liftT3 f a b c <*> (optional whitespace *> d)

-- Non back-tracking
many :: Parser p -> Parser [p]
many p = liftA2 (:) (try p) (many p) <|> pure []

some :: Parser p -> Parser [p]
some p = liftA2 (:) p (many p)

lit :: Parser (T Exp)
lit = token lit' <?> "literal"
  where lit' (Token.Lit x) = Just (Parse.Lit x)
        lit' _             = Nothing

qvarid :: Parser QString
qvarid = token qvarid' <?> "qvarid"
  where qvarid' (Token.QVarId n) = Just n
        qvarid' _                = Nothing

varid :: Parser String
varid = token varid' <?> "varid"
  where varid' (Token.QVarId n) | qualification n == [] = Just (name n)
        varid' _                                        = Nothing

reservedId :: String -> Parser ()
reservedId s = satisfy reservedId' *> pure () <?> "reserved id '" ++ s ++ "'"
  where reservedId' (Token.ReservedId s') | s == s' = True
        reservedId' _                               = False

reservedOp :: String -> Parser ()
reservedOp s = satisfy reservedOp' *> pure () <?> "reserved op '" ++ s ++ "'"
  where reservedOp' (Token.ReservedOp s') | s == s' = True
        reservedOp' _                               = False

-- |The primary function, which attempts to parse a string to an annotated sugared AST
parse :: Compiler ()
parse = do
  set stage Parse
  ts <- get tokens
  case runParser program ts of
    Left e    -> throwError e
    Right ast -> set sugaredAST ast >> debugPrint ast

program :: Parser (T Exp)
program = optional whitespace *> exp <* optional whitespace

exp :: Parser (T Exp)
exp = letExp <|> varExp <|> literal <|?> "exp"

varExp :: Parser (T Exp)
varExp = Var <$> try varid <?> "var" -- TODO should be qvarid

whitespace :: Parser ()
whitespace = try (token whitespace') <?> "whitespace"
  where whitespace' Token.Whitespace = Just ()
        whitespace' _                = Nothing

literal :: Parser (T Exp)
literal = try (token literal') <?> "literal"
  where literal' (Token.Lit x) = Just (Parse.Lit x)
        literal' _             = Nothing

decl :: Parser (T Decl)
decl = liftT3 (\n _ e -> FunDecl n e) varid (reservedOp "=") (annotated exp) <?> "decl"  -- TODO

letExp :: Parser (T Exp)
letExp = liftT4 (\_ x _ e -> Parse.Let x e) (try (reservedId "let")) (annotated decl) (reservedId "in") (annotated exp) <?> "let expression"
{-
block :: Parser a -> Parser [a]
block p = braces (sepBy1 p semi)

-- |sepBy1' is similar to sepBy1 except it includes the separator in the result
sepBy1' :: Parser a -> Parser a -> Parser [a]
sepBy1' p sep = liftA2 (:) p (concat <$> many (liftA2 join sep p))
  where join x y = [x,y]

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
