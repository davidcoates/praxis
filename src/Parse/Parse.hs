{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Parse.Parse
  ( Parseable(..)
  ) where

import           AST
import           Common
import           Introspect           (Recursive)
import           Parse.Annotate
import           Parse.Parse.Parser
import           Parse.Tokenise.Token (Token (..))
import qualified Parse.Tokenise.Token as Token
import           Praxis               hiding (try)
import           Record               (Record)
import qualified Record
import           Stage                (Parse)
import           Type

import           Control.Applicative  (Const (..), liftA2, liftA3, (<**>),
                                       (<|>))
import qualified Control.Applicative  as Applicative (empty)
import           Control.Lens         (view)
import           Data.Maybe           (fromJust, isJust)
import qualified Data.Set             as Set
import           Prelude              hiding (exp, log)

class Parseable a where
  parse  :: [Sourced Token] -> Praxis (Parsed a)

parse' :: Recursive a => Parser (a Parse) -> [Sourced Token] -> Praxis (Parsed a)
parse' parser ts = save stage $ do
  stage .= Parse
  x <- runParser parser ts
  log Debug x
  return x

instance Parseable Program where
  parse = parse' program

instance Parseable Exp where
  parse = parse' exp

instance Parseable Type where
  parse = parse' ty

instance Parseable Kind where
  parse = parse' kind

-- TODO consistent backtracing

-- Non back-tracking
optional :: Parser a -> Parser (Maybe a)
optional p = Just <$> p <|> pure Nothing

many :: Parser p -> Parser [p]
many p = (:) <$> try p <*> many p <|> pure []

many1 :: Parser p -> Parser [p]
many1 p = (:) <$> p <*> many p

some :: Parser p -> Parser [p]
some p = (:) <$> p <*> many p

sepBy1 :: Parser a -> Parser b -> Parser [a]
sepBy1 p sep = (:) <$> p <*> many (sep *> p)

qconid :: Parser QString
qconid = token qconid' <?> "qconid"
  where qconid' (Token.QConId n) = Just n
        qconid' _                = Nothing

conid :: Parser String
conid = token conid' <?> "conid"
  where conid' (Token.QConId n) | null (qualification n) = Just (name n)
        conid' _                = Nothing

qvarid :: Parser QString
qvarid = token qvarid' <?> "qvarid"
  where qvarid' (Token.QVarId n) = Just n
        qvarid' _                = Nothing

varid :: Parser String
varid = token varid' <?> "varid"
  where varid' (Token.QVarId n) | null (qualification n) = Just (name n)
        varid' _                = Nothing

qvarsym :: Parser QString
qvarsym = token qvarsym' <?> "qvarsym"
  where qvarsym' (Token.QVarSym n) = Just n
        qvarsym' _                 = Nothing

varsym :: Parser String
varsym = token varsym' <?> "varsym"
  where varsym' (Token.QVarSym n) | null (qualification n) = Just (name n)
        varsym' _                 = Nothing

-- We don't want to reserve some operators, namely forall . and constrant +
userOp :: String -> Parser ()
userOp s = token userOp' *> pure () <?> "op '" ++ s ++ "'"
  where userOp' (Token.QVarSym n) | null (qualification n) && name n == s = Just ()
        userOp' _ = Nothing

plus :: Parser ()
plus = userOp "+"

dot :: Parser ()
dot = userOp "."

reservedId :: String -> Parser ()
reservedId s = satisfy reservedId' *> pure () <?> "reserved id '" ++ s ++ "'"
  where reservedId' (Token.ReservedId s') | s == s' = True
        reservedId' _                     = False

reservedCon :: String -> Parser ()
reservedCon s = satisfy reservedCon' *> pure () <?> "reserved con '" ++ s ++ "'"
  where reservedCon' (Token.ReservedCon s') | s == s' = True
        reservedCon' _                      = False

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
block p = (:) <$> (lbrace *> p) <*> block'
  where block' = (try rbrace *> pure []) <|> (:) <$> (semi *> p) <*> block'

program :: Parser (Program Parse)
program = Program <$> block (parsed topDecl)

topDecl :: Parser (Decl Parse)
topDecl = decl <|?> "topDecl" -- TODO

decl :: Parser (Decl Parse)
decl = funType <|> funDecl <|?> "decl"

funType :: Parser (Decl Parse)
funType = DeclSig <$> try prefix <*> sig <|?> "funType"
  where prefix = varid <* reservedOp ":"

funDecl :: Parser (Decl Parse)
funDecl = try prefix <*> parsed exp <?> "funDecl"
  where prefix = (\v ps _ -> DeclFun v ps) <$> varid <*> many (parsed pat) <*> reservedOp "="

exp :: Parser (Exp Parse)
exp = mixfixexp
{- liftA2 f (parsed mixfixexp) (optionMaybe sig)
  where sig = reservedOp ":" *> ty
        f (_ :< e) Nothing  = e
        f e (Just t) = Sig e t
-}

left :: (a -> a -> a) -> Parser [a] -> Parser a
left f p = unroll <$> p
  where unroll [x]      = x
        unroll (x:y:ys) = unroll (f x y : ys)

leftT :: (Parsed a -> Parsed a -> a Parse) -> Parser [Parsed a] -> Parser (a Parse)
leftT f p = view value <$> left (\x y -> view tag x :< f x y) p

mixfixexp :: Parser (Exp Parse)
mixfixexp = Mixfix <$> some (try top <|> texp)
  where top = (\t -> view tag t :< TOp (view value t)) <$> parsed qop
        texp = (\t -> view tag t :< TExp t) <$> parsed lexp

qop :: Parser Op
qop = qvarsym -- TODO

-- TODO should do be here?
lexp :: Parser (Exp Parse)
lexp = expRead <|> expDo <|> expCase <|> expCases <|> fexp <|?> "lexp"

fexp :: Parser (Exp Parse)
fexp = leftT Apply (some (parsed aexp))

aexp :: Parser (Exp Parse)
aexp = expRecord <|> parens <|> expVar <|> expLit <|?> "aexp"
  where parens = try (special '(') *> exp <* special ')'

stmt :: Parser (Stmt Parse)
stmt = try (StmtDecl <$> parsed decl) <|> (StmtExp <$> parsed exp)

alt = (,) <$> parsed pat <*> (reservedOp "->" *> parsed exp)

expCase :: Parser (Exp Parse)
expCase = Case <$> (try (reservedId "case") *> parsed exp) <*> (reservedId "of" *> block alt)

expCases :: Parser (Exp Parse)
expCases = Cases <$> (try (reservedId "cases") *> block alt)

expDo :: Parser (Exp Parse)
expDo = Do <$> (try (reservedId "do") *> block (parsed stmt))

expVar :: Parser (Exp Parse)
expVar = Var <$> try varid <?> "var" -- TODO should be qvarid

expLit :: Parser (Exp Parse)
expLit = AST.Lit <$> lit

expRecord :: Parser (Exp Parse)
expRecord = Record <$> record '(' ')' (parsed exp)

lit :: Parser AST.Lit
lit = try (token lit') <?> "literal"
  where lit' (Token.Lit x) = Just x
        lit' _             = Nothing

pat :: Parser (Pat Parse)
pat = patHole <|> patVar <|> patLit <|> patRecord <|?> "pat"

patHole :: Parser (Pat Parse)
patHole = try (special '_') *> return PatHole

patRecord :: Parser (Pat Parse)
patRecord = PatRecord <$> record '(' ')' (parsed pat)

patVar :: Parser (Pat Parse)
patVar = PatVar <$> try varid

patLit :: Parser (Pat Parse)
patLit = PatLit <$> lit

expRead :: Parser (Exp Parse)
expRead = Read <$> (try prefix *> varid) <*> (reservedId "in" *> parsed exp) <?> "read expression"
  where prefix = reservedId "read"

raw a = (Phantom, ()) :< a

sig :: Parser (Parsed Type)
sig = parsed ty
{-
sig :: Parser (Parsed QType)
sig = parsed qty <|> ((\(a :< p) -> (a :< Mono (a :< p))) <$> parsed ty)
  where qty :: Parser (QType Parse)
        qty = Forall <$> (try (reservedId "forall" *> many1 var) <*> (dot *> constraints) <*> parsed ty
        constraints :: Parser (Parsed Type)
        constraints = parsed $ pure empty      -- TODO constraints
        var = (,) <$> varid <*> pure KindType -- TODO allow kinds
-}

empty :: Type Parse
empty = TyFlat Set.empty

ty :: Parser (Type Parse)
ty = f <$> parsed ty' <*> optional (try (reservedOp "->") *> parsed ty)
  where f :: Parsed Type -> Maybe (Parsed Type) -> Type Parse
        f p Nothing   = view value p
        f p (Just p') = TyApply (raw (TyCon "->")) (raw (TyPack (Record.pair p p'))) -- TODO sources
        ty' = tyVar <|> tyCon <|> tyRecord <|> tyParen
        tyParen = special '(' *> ty <* special ')'

tyRecord :: Parser (Type Parse)
tyRecord = TyRecord <$> record '(' ')' (parsed ty)

tyVar :: Parser (Type Parse)
tyVar = TyVar <$> try varid

tyCon :: Parser (Type Parse)
tyCon = TyCon <$> try conid

kind :: Parser (Kind Parse)
kind = f <$> parsed kind' <*> optional (try (reservedOp "->") *> parsed kind)
  where f :: Parsed Kind -> Maybe (Parsed Kind) -> Kind Parse
        f p Nothing   = view value p
        f p (Just p') = KindFun p p'
        kind' = kindType <|> kindConstraint <|> kindRecord <|> kindParen
        kindParen = special '(' *> kind <* special ')'

kindType :: Parser (Kind Parse)
kindType = try (reservedCon "Type") *> pure KindType

kindConstraint :: Parser (Kind Parse)
kindConstraint = try (reservedCon "Constraint") *> pure KindConstraint

kindRecord :: Parser (Kind Parse)
kindRecord = KindRecord <$> record '[' ']' (parsed kind)

-- FIXME (add optional fields)
record :: Char -> Char -> Parser (Parsed a) -> Parser (Record (Parsed a))
record l r p = Record.fromList . zip (repeat Nothing) <$> recordList where
  recordList = try (special l *> special r) *> pure [] <|> ((:) <$> try (special l *> p <* special ',') <*> rest)
  rest = sepBy1 p (special ',') <* special r

