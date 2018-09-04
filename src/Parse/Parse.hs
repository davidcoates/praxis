{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Parse.Parse
  ( Parseable(..)
  ) where

import           AST                  (Lit (..), QString (..))
import           Parse.Parse.AST      (Annotated (..))
import           Parse.Parse.AST      as Parse
import           Parse.Parse.Parser
import           Parse.Tokenise.Token (Token (..))
import qualified Parse.Tokenise.Token as Token
import           Praxis               hiding (try)
import           Record               (Record)
import qualified Record
import           Source
import           Tag
import           Type

import           Control.Applicative  (liftA2, liftA3, (<**>), (<|>))
import qualified Control.Applicative  as Applicative (empty)
import           Control.Lens         (view)
import           Data.Maybe           (fromJust, isJust)
import qualified Data.Set             as Set
import           Prelude              hiding (exp, log)

type T a = a (Tag Source)

class Parseable a where
  parse  :: [Token.Annotated Token] -> Praxis a

parse' :: Show (Annotated a) => Parser (T a) -> [Token.Annotated Token] -> Praxis (Annotated a)
parse' parser ts = save stage $ do
  set stage Parse
  x <- runParser parser ts
  log Debug x
  return x

instance Parseable (Annotated Program) where
  parse = parse' program

instance Parseable (Annotated Exp) where
  parse = parse' exp

instance Parseable (Annotated Type) where
  parse = parse' ty

instance Parseable Kind where
  parse ts = save stage $ do
    set stage Parse
    _ :< x <- runParser kind ts
    log Debug x
    return x


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

some :: Parser p -> Parser [p]
some p = liftT2 (:) p (many p)

sepBy1 :: Parser a -> Parser b -> Parser [a]
sepBy1 p sep = liftT2 (:) p (many (sep #> p))

sepBy2 :: Parser a -> Parser b -> Parser [a]
sepBy2 p sep = liftT2 (:) p (sep #> sepBy1 p sep)

qconid :: Parser QString
qconid = token qconid' <?> "qconid|"
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

plus :: Parser () -- TODO this is a bit of an awkward hack, since we don't want to reserve +
plus = token plus' <?> "effect +"
  where plus' (Token.QVarSym n) | null (qualification n) && name n == "+" = Just ()
        plus' _                 = Nothing

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
topDecl = decl <|?> "topDecl" -- TODO

decl :: Parser (T Decl)
decl = funType <|> funDecl <|?> "decl"

funType :: Parser (T Decl)
funType = liftT2 DeclSig (try prefix) (annotated impure) <|?> "funType"
  where prefix = varid <# reservedOp ":"

funDecl :: Parser (T Decl)
funDecl = liftT2 ($) (try prefix) (annotated exp) <?> "funDecl"
  where prefix = liftT3 (\v ps _ -> DeclFun v ps) varid (many (annotated pat)) (reservedOp "=")

exp :: Parser (T Exp)
exp = mixfixexp
{- liftT2 f (annotated mixfixexp) (optionMaybe sig)
  where sig = reservedOp ":" #> ty
        f (_ :< e) Nothing  = e
        f e (Just t) = Sig e t
-}

left :: (a -> a -> a) -> Parser [a] -> Parser a
left f p = unroll <$> p
  where unroll [x]      = x
        unroll (x:y:ys) = unroll (f x y : ys)

leftT :: (Annotated a -> Annotated a -> T a) -> Parser [Annotated a] -> Parser (T a)
leftT f p = value <$> left (\x y -> tag x :< f x y) p

mixfixexp :: Parser (T Exp)
mixfixexp = Mixfix <$> some (try top <|> texp)
  where top = (\t -> tag t :< TOp (value t)) <$> annotated qop
        texp = (\t -> tag t :< TExp t) <$> annotated lexp

qop :: Parser Op
qop = qvarsym -- TODO

-- TODO should do be here?
lexp :: Parser (T Exp)
lexp = expRead <|> expDo <|> expCases <|> fexp <|?> "lexp"

fexp :: Parser (T Exp)
fexp = leftT Apply (some (annotated aexp))

aexp :: Parser (T Exp)
aexp = expRecord <|> parens <|> expVar <|> expLit <|?> "aexp"
  where parens = liftT3 (\_ e _ -> e) (try (special '(')) exp (special ')')

stmt :: Parser (T Stmt)
stmt = try (StmtDecl <$> annotated decl) <|> (StmtExp <$> annotated exp)

expCases :: Parser (T Exp)
expCases = Cases <$> (try (reservedId "cases") #> block alt)
  where alt = liftT2 (,) (annotated pat) (reservedOp "->" #> annotated exp)

expDo :: Parser (T Exp)
expDo = Do <$> (try (reservedId "do") #> block (annotated stmt))

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

pat :: Parser (T Pat)
pat = patHole <|> patVar <|> patLit <|> patRecord <|?> "pat"

unit :: Parser ()
unit = try (special '(' #> special ')') *> return ()

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

impure :: Parser (T Impure)
impure = liftT2O f (annotated ty) (reservedOp "#") (annotated effs) <|?> "ty"
  where f p Nothing   = p :# (Phantom :< TyEffects Set.empty)
        f p (Just es) = p :# es

effs :: Parser (T Type)
effs = TyEffects . Set.fromList <$> sepBy1 (annotated eff) plus

eff :: Parser (T Type)
eff = efLit <|> efVar <?> "effect"
  where efLit = TyCon <$> try conid
        efVar = TyVar <$> try varid

ty :: Parser (T Type)
ty = liftT2O f (annotated ty') (reservedOp "->") impure
  where f p Nothing          = value p
        f p (Just (p' :# e)) = TyApply (Phantom :< TyCon "->") (Phantom :< TyPack (Record.triple p p' e)) -- TODO sources
        ty' = tyUnit <|> tyVar <|> tyCon <|> tyRecord <|> tyParen
        tyParen = special '(' #> ty <# special ')'

tyRecord :: Parser (T Type)
tyRecord = TyRecord <$> record (annotated ty)

tyUnit :: Parser (T Type)
tyUnit = unit *> return (TyRecord Record.unit)

tyVar :: Parser (T Type)
tyVar = TyVar <$> try varid

tyCon :: Parser (T Type)
tyCon = TyCon <$> try conid

kind :: Parser Kind
kind = undefined -- FIXME

record :: Parser (Annotated a) -> Parser (Record (Annotated a))
record p = try (special '(' #> guts <# special ')')
  where guts = (Record.fromList . zip (repeat Nothing)) <$> sepBy2 p (special ',') -- FIXME (add optional fields)

