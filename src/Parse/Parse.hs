{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Parse.Parse
  ( parse

  , parseFree
  , Parseable
  -- , module Parse.Parse.AST
  ) where

import           Parse.Parse.AST      as Parse
import           Parse.Parse.Parser
import           Parse.Tokenise.Token as Token

import           Compiler
import qualified Record
import           Source
import           Tag
import           Type

import           Control.Applicative  (liftA2, liftA3, (<**>), (<|>))
import qualified Control.Applicative  as Applicative (empty)
import           Control.Lens         (view)
import           Data.Maybe           (fromJust, isJust)
import qualified Data.Set             as Set (fromList)
import           Prelude              hiding (exp)

import           AST                  (QString (..))

class Parseable a where
  parser :: Parser a

type T a = a (Tag Source)

instance Parseable (T Program) where
  parser = program

instance Parseable Type where
  parser = ty

parseFree :: Parseable a => Compiler (Tag Source a)
parseFree = save stage $ do
  set stage Parse
  ts <- get tokens
  runParser parser ts

parse :: Compiler ()
parse = save stage $ do
  set stage Parse
  p <- parseFree
  set sugaredAST p
  debugPrint p

-- TODO move these to Parse/Parser?
optional :: Parser a -> Parser ()
optional p = p *> pure () <|> pure ()

optionMaybe :: Parser a -> Parser (Maybe a)
optionMaybe p = (Just <$> p) <|> pure Nothing

liftT2 :: (a -> b -> c) -> Parser a -> Parser b -> Parser c
liftT2 f a b = liftA2 f a (optional whitespace *> b)

liftT3 :: (a -> b -> c -> d) -> Parser a -> Parser b -> Parser c -> Parser d
liftT3 f a b c = liftT2 f a b <*> (optional whitespace *> c)

liftT4 :: (a -> b -> c -> d -> e) -> Parser a -> Parser b -> Parser c -> Parser d -> Parser e
liftT4 f a b c d = liftT3 f a b c <*> (optional whitespace *> d)

liftT2O :: (a -> b -> c) -> Parser a -> b -> Parser b -> Parser c
liftT2O f pa b pb = liftA2 f pa (try (optional whitespace *> pb) <|> pure b)

liftT2M :: (a -> b -> a) -> Parser a -> Parser b -> Parser a
liftT2M f pa pb = liftT2O f' pa Nothing (Just <$> pb)
  where f' a (Just b) = f a b
        f' a Nothing  = a

(#>) :: Parser a -> Parser b -> Parser b
(#>) = liftT2 (\_ b -> b)

(<#) :: Parser a -> Parser b -> Parser a
(<#) = liftT2 (\a _ -> a)

-- TODO consistent backtracing

-- Non back-tracking
many :: Parser p -> Parser [p]
many p = liftT2 (:) (try p) (many p) <|> pure []

some :: Parser p -> Parser [p]
some p = liftT2 (:) p (many p)

sepBy1 :: Parser a -> Parser b -> Parser [a]
sepBy1 p sep = liftT2 (:) p (many (liftT2 (\_ p -> p) sep p))

qconid :: Parser QString
qconid = token qconid' <?> "qconid"
  where qconid' (Token.QConId n) = Just n
        qconid' _                = Nothing

conid :: Parser String
conid = token conid' <?> "conid"
  where conid' (Token.QConId n) | qualification n == [] = Just (name n)
        conid' _                = Nothing

qvarid :: Parser QString
qvarid = token qvarid' <?> "qvarid"
  where qvarid' (Token.QVarId n) = Just n
        qvarid' _                = Nothing

varid :: Parser String
varid = token varid' <?> "varid"
  where varid' (Token.QVarId n) | qualification n == [] = Just (name n)
        varid' _                = Nothing

qvarsym :: Parser QString
qvarsym = token qvarsym' <?> "qvarsym"
  where qvarsym' (Token.QVarSym n) = Just n
        qvarsym' _                 = Nothing

varsym :: Parser String
varsym = token varsym' <?> "varsym"
  where varsym' (Token.QVarSym n) | qualification n == [] = Just (name n)
        varsym' _                 = Nothing

reservedId :: String -> Parser ()
reservedId s = satisfy reservedId' *> pure () <?> "reserved id '" ++ s ++ "'"
  where reservedId' (Token.ReservedId s') | s == s' = True
        reservedId' _                     = False

reservedOp :: String -> Parser ()
reservedOp s = satisfy reservedOp' *> pure () <?> "reserved op '" ++ s ++ "'"
  where reservedOp' (Token.ReservedOp s') | s == s' = True
        reservedOp' _                     = False

special :: Char -> Parser ()
special c = satisfy special' *> pure () <?> "special '" ++ [c] ++ "'"
  where special' (Token.Special c') | c == c' = True
        special' _                  = False

lbrace :: Parser ()
lbrace = special '{'

rbrace :: Parser ()
rbrace = special '}'

semi :: Parser ()
semi = special ';'

block :: Parser a -> Parser [a]
block p = liftT3 (\_ p ps -> p:ps) lbrace p block'
  where block' = (try rbrace *> pure []) <|> liftT2 (:) (semi #> p) block'


program :: Parser (T Program)
program = fmap Program (optional whitespace *> block (annotated topDecl) <* optional whitespace)

topDecl :: Parser (T Decl)
topDecl = funType <|> funDecl <|?> "topDecl"

funType :: Parser (T Decl)
funType = liftT2 ($) (try prefix) ty <?> "funType"
  where prefix = liftT2 (\v _ -> DeclSig v) varid (reservedOp ":")

funDecl :: Parser (T Decl)
funDecl = liftT2 ($) (try prefix) (annotated exp) <?> "funDecl"
  where prefix = liftT3 (\v ps _ -> DeclFun v ps) varid (many (annotated pat)) (reservedOp "=")

exp :: Parser (T Exp)
exp = mixfixexp

left :: (a -> a -> a) -> Parser [a] -> Parser a
left f p = unroll <$> p
  where unroll [x]      = x
        unroll (x:y:ys) = unroll ((f x y):ys)

leftT :: (Parse.Annotated a -> Parse.Annotated a -> T a) -> Parser [Parse.Annotated a] -> Parser (T a)
leftT f p = value <$> left (\x y -> tag x :< f x y) p

mixfixexp :: Parser (T Exp)
mixfixexp = Mixfix <$> some (try top <|> texp)
  where top = (\t -> tag t :< TOp (value t)) <$> annotated qop
        texp = (\t -> tag t :< TExp t) <$> annotated lexp

qop :: Parser Op
qop = qvarsym -- TODO

lexp :: Parser (T Exp)
lexp = expRead <|> fexp <|?> "lexp"

fexp :: Parser (T Exp)
fexp = leftT Apply (some (annotated aexp))

aexp :: Parser (T Exp)
aexp = expRecord <|> parens <|> expVar <|> expLit <|?> "aexp"
  where parens = liftT3 (\_ e _ -> e) (try (special '(')) exp (special ')')

expVar :: Parser (T Exp)
expVar = Var <$> try varid <?> "var" -- TODO should be qvarid

expLit :: Parser (T Exp)
expLit = Parse.Lit <$> lit

expRecord :: Parser (T Exp)
expRecord = expUnit -- TODO
  where expUnit = unit *> pure (Record Record.unit)

whitespace :: Parser ()
whitespace = try (token whitespace') <?> "whitespace"
  where whitespace' Token.Whitespace = Just ()
        whitespace' _                = Nothing

lit :: Parser Lit
lit = try (token lit') <?> "literal"
  where lit' (Token.Lit x) = Just x
        lit' _             = Nothing

decl :: Parser (T Decl)
decl = liftT4 (\n ps _ e -> DeclFun n ps e) varid (some (annotated pat)) (reservedOp "=") (annotated exp) <?> "decl"  -- TODO

pat :: Parser (T Pat)
pat = patHole <|> patVar <|> patLit <|> patRecord <|?> "pat"

unit :: Parser ()
unit = try (special '(' *> special ')') *> return () -- Note: No whitespace

patHole :: Parser (T Pat)
patHole = try (special '_') *> return PatHole

patRecord :: Parser (T Pat)
patRecord = patUnit -- TODO
  where patUnit :: Parser (T Pat)
        patUnit = unit *> return (PatRecord Record.unit)

patVar :: Parser (T Pat)
patVar = PatVar <$> try varid

patLit :: Parser (T Pat)
patLit = PatLit <$> lit

expRead :: Parser (T Exp)
expRead = liftT4 (\_ x _ e -> Parse.Read x e) (try prefix) varid (reservedId "in") (annotated exp) <?> "read expression"
  where prefix = reservedId "read"

ty :: Parser Type
ty = liftT2O (:#) tyPure empty (reservedOp "#" #> effs)

effs :: Parser Effects
effs = Set.fromList <$> sepBy1 eff (special ',')

eff :: Parser Effect
eff = EfLit <$> conid -- TODO vars, qualified effects?

tyPure :: Parser Pure
tyPure = liftT2O join tyPure' Nothing (reservedOp "->" #> (Just <$> ty)) <?> "tyPure"
  where join :: Pure -> Maybe Type -> Pure
        join p Nothing  = p
        join p (Just t) = TyFun p t
        tyPure' = try tyUnit <|> tyPrim

tyUnit :: Parser Pure
tyUnit = unit *> return (TyRecord Record.unit)

tyPrim :: Parser Pure
tyPrim = TyPrim <$> do
  s <- conid
  case s of
    "Bool"   -> return TyBool
    "Char"   -> return TyChar
    "Int"    -> return TyInt
    "String" -> return TyString
    _        -> Applicative.empty
