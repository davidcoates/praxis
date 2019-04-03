{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Parse.Parse
  ( Parseable(..)
  ) where

import           AST                  (Lit (..), QString (..))
import           Common
import           Parse.Annotate
import           Parse.Parse.AST      as Parse
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

parse' :: Show (Parsed a) => Parser (a Parse) -> [Sourced Token] -> Praxis (Parsed a)
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

instance Parseable (Const Kind) where
  parse ts = save stage $ do
    stage .= Parse
    a :< x <- runParser kind ts
    log Debug x
    return (a :< Const x)


-- TODO move these to Parse/Parser?
optional :: Parser a -> Parser ()
optional p = p *> pure () <|> pure ()

liftT2 :: (a -> b -> c) -> Parser a -> Parser b -> Parser c
liftT2 f a b = liftA2 f a (optional whitespace *> b)

liftT3 :: (a -> b -> c -> d) -> Parser a -> Parser b -> Parser c -> Parser d
liftT3 f a b c = liftT2 f a b <*> (optional whitespace *> c)

liftT4 :: (a -> b -> c -> d -> e) -> Parser a -> Parser b -> Parser c -> Parser d -> Parser e
liftT4 f a b c d = liftT3 f a b c <*> (optional whitespace *> d)

liftT2O :: (a -> Maybe b -> c) -> Parser a -> Parser s -> Parser b -> Parser c
liftT2O f pa ps pc = liftA2 f pa ((Just <$> (try (optional whitespace *> ps) #> pc)) <|> pure Nothing)

(#>) :: Parser a -> Parser b -> Parser b
(#>) = liftT2 (\_ b -> b)

(<#) :: Parser a -> Parser b -> Parser a
(<#) = liftT2 (\a _ -> a)

-- TODO consistent backtracing

-- Non back-tracking
many :: Parser p -> Parser [p]
many p = liftT2 (:) (try p) (many p) <|> pure []

many1 :: Parser p -> Parser [p]
many1 p = liftT2 (:) p (many p)

some :: Parser p -> Parser [p]
some p = liftT2 (:) p (many p)

sepBy1 :: Parser a -> Parser b -> Parser [a]
sepBy1 p sep = liftT2 (:) p (many (sep #> p))

sepBy2 :: Parser a -> Parser b -> Parser [a]
sepBy2 p sep = liftT2 (:) p (sep #> sepBy1 p sep)

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

program :: Parser (Program Parse)
program = fmap Program (optional whitespace *> block (parsed topDecl) <* optional whitespace)

topDecl :: Parser (Decl Parse)
topDecl = decl <|?> "topDecl" -- TODO

decl :: Parser (Decl Parse)
decl = funType <|> funDecl <|?> "decl"

funType :: Parser (Decl Parse)
funType = liftT2 DeclSig (try prefix) sig <|?> "funType"
  where prefix = varid <# reservedOp ":"

funDecl :: Parser (Decl Parse)
funDecl = liftT2 ($) (try prefix) (parsed exp) <?> "funDecl"
  where prefix = liftT3 (\v ps _ -> DeclFun v ps) varid (many (parsed pat)) (reservedOp "=")

exp :: Parser (Exp Parse)
exp = mixfixexp
{- liftT2 f (parsed mixfixexp) (optionMaybe sig)
  where sig = reservedOp ":" #> ty
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
  where parens = liftT3 (\_ e _ -> e) (try (special '(')) exp (special ')')

stmt :: Parser (Stmt Parse)
stmt = try (StmtDecl <$> parsed decl) <|> (StmtExp <$> parsed exp)

alt = liftT2 (,) (parsed pat) (reservedOp "->" #> parsed exp)

expCase :: Parser (Exp Parse)
expCase = Case <$> (try (reservedId "case") #> parsed exp) <*> (reservedId "of" #> block alt)

expCases :: Parser (Exp Parse)
expCases = Cases <$> (try (reservedId "cases") #> block alt)

expDo :: Parser (Exp Parse)
expDo = Do <$> (try (reservedId "do") #> block (parsed stmt))

expVar :: Parser (Exp Parse)
expVar = Var <$> try varid <?> "var" -- TODO should be qvarid

expLit :: Parser (Exp Parse)
expLit = Parse.Lit <$> lit

expRecord :: Parser (Exp Parse)
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

pat :: Parser (Pat Parse)
pat = patHole <|> patVar <|> patLit <|> patRecord <|?> "pat"

unit :: Parser ()
unit = try (special '(' #> special ')') *> return ()

patHole :: Parser (Pat Parse)
patHole = try (special '_') *> return PatHole

patRecord :: Parser (Pat Parse)
patRecord = patUnit -- TODO
  where patUnit :: Parser (Pat Parse)
        patUnit = unit *> return (PatRecord Record.unit)

patVar :: Parser (Pat Parse)
patVar = PatVar <$> try varid

patLit :: Parser (Pat Parse)
patLit = PatLit <$> lit

expRead :: Parser (Exp Parse)
expRead = liftT4 (\_ x _ e -> Parse.Read x e) (try prefix) varid (reservedId "in") (parsed exp) <?> "read expression"
  where prefix = reservedId "read"

raw a = (Phantom, ()) :< a

sig :: Parser (Parsed QType)
sig = parsed qty <|> ((\(a :< p) -> (a :< Mono (a :< p))) <$> parsed ty)
  where qty :: Parser (QType Parse)
        qty = try (reservedId "forall") #> liftT3 Forall (many1 var <# dot) constraints (parsed ty)
        constraints :: Parser (Parsed Type)
        constraints = parsed $ pure empty      -- TODO constraints
        var = liftT2 (,) varid (pure KindType) -- TODO allow kinds

empty :: Type Parse
empty = TyFlat Set.empty

ty :: Parser (Type Parse)
ty = liftT2O f (parsed ty') (reservedOp "->") (parsed ty)
  where f :: Parsed Type -> Maybe (Parsed Type) -> Type Parse
        f p Nothing   = view value p
        f p (Just p') = TyApply (raw (TyCon "->")) (raw (TyPack (Record.pair p p'))) -- TODO sources
        ty' = tyUnit <|> tyVar <|> tyCon <|> tyRecord <|> tyParen
        tyParen = special '(' #> ty <# special ')'

tyRecord :: Parser (Type Parse)
tyRecord = TyRecord <$> record (parsed ty)

tyUnit :: Parser (Type Parse)
tyUnit = unit *> return (TyRecord Record.unit)

tyVar :: Parser (Type Parse)
tyVar = TyVar <$> try varid

tyCon :: Parser (Type Parse)
tyCon = TyCon <$> try conid

kind :: Parser Kind
kind = undefined -- FIXME

record :: Parser (Parsed a) -> Parser (Record (Parsed a))
record p = try (special '(' #> guts <# special ')')
  where guts = (Record.fromList . zip (repeat Nothing)) <$> sepBy2 p (special ',') -- FIXME (add optional fields)

