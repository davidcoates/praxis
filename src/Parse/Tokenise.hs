module Parse.Tokenise
  ( run
  ) where

import           Common                   hiding (asum)
import           Parse.Tokenise.Tokeniser hiding (run)
import qualified Parse.Tokenise.Tokeniser as Tokeniser (run)
import           Parse.Tokenise.Unlayout
import           Praxis                   hiding (throw)
import qualified Stage
import           Term                     (Lit (..), ViewDomain (..))
import           Token

import           Control.Applicative      (Alternative (..), Applicative (..))
import           Data.Foldable            (asum)
import           Data.List                (intercalate)
import           Data.Maybe               (fromJust)
import           Prelude                  hiding (until)

run :: Bool -> String -> Praxis [Sourced Token]
run topLevel text = save stage $ do
  stage .= Stage.Tokenise
  tokens <- Tokeniser.run token text
  display (separate " " (map (view value) tokens)) `ifFlag` debug
  stage .= Stage.Layout
  let tokens' = unlayout topLevel tokens
  display (separate " " (map (view value) tokens')) `ifFlag` debug
  return tokens'

-- Helper functions
until :: Tokeniser a -> Tokeniser b -> Tokeniser [b]
until p t = (p *> pure []) <|> ((:) <$> t <*> until p t)

while :: Tokeniser a -> Tokeniser b -> Tokeniser [b]
while p t = (p *> ((:) <$> t <*> while p t)) <|> pure []

char :: Char -> Tokeniser Char
char c = match (== c)

isSymbol = (`elem` "!#$%&*+./<=>?@\\^|-~:[]")
isLower = (`elem` ['a'..'z'])
isUpper = (`elem` ['A'..'Z'])
isDigit = (`elem` ['0'..'9'])
isSpace = (`elem` " \t")
isAlphaNum c = isLower c || isUpper c || isDigit c
isLetter c = c `elem` "_\'" || isAlphaNum c

token :: Tokeniser (Maybe Token)
token = (whitespace *> pure Nothing) <|> (Just <$> (layout <|> special <|> semiSpecial <|> literal <|> stuff)) <|> throw "illegal character"

whitespace :: Tokeniser ()
whitespace = newline <|> space <|> comment
  where newline = match (`elem` "\r\n\f") *> pure ()
        space = match isSpace *> pure ()
        comment = satisfies 3 (\[a, b, c] -> a == '-' && b == '-' && not (isSymbol c)) *> until newline consume *> pure ()

layout :: Tokeniser Token
layout = Layout <$> match (`elem` "{};")

special :: Tokeniser Token
special = Special <$> match (`elem` "(),`_")

-- AKA contextually reserved operators.
-- We want to treat them like special symbols for lexing (so e.g. "[&" lexes as two tokens, not one)
semiSpecial :: Tokeniser Token
semiSpecial = (\s -> QVarSym Qualified { qualification = [], unqualify = [s]}) <$> match (`elem` "[].") -- TODO qualification

literal :: Tokeniser Token
literal = intLiteral <|> charLiteral <|> stringLiteral

intLiteral :: Tokeniser Token
intLiteral = satisfy isDigit *> (Lit . Int <$> decimal)
  where decimal :: Tokeniser Int
        decimal = read <$> while (satisfy isDigit) consume

charEscapeSeqs = [
  ('0', '\0'),
  ('a', '\a'),
  ('b', '\b'),
  ('f', '\f'),
  ('n', '\n'),
  ('r', '\r'),
  ('t', '\t'),
  ('v', '\v'),
  ('\"', '"'),
  ('\'', '\''),
  ('\\', '\\')]

stringEscapeSeqs = ('&', "") : map (\(a, b) -> (a, b:[])) charEscapeSeqs

escape :: [(Char, a)] -> Tokeniser a
escape seqs = char '\\' *> (seq <|> throw "invalid escape sequence") where
    seq = satisfy (\c -> c `elem` map fst seqs) *> ((\c -> fromJust (c `lookup` seqs)) <$> consume)

charLiteral :: Tokeniser Token
charLiteral = char '\'' *> ((Lit . Char <$> inner) <* char '\'' <|> throw "unterminated character literal") where
  inner :: Tokeniser Char
  inner = escape charEscapeSeqs <|> match (/= '\'')

stringLiteral :: Tokeniser Token
stringLiteral = char '"' *> ((Lit . String <$> inner) <* char '"' <|> throw "unterminated string literal") where
  inner :: Tokeniser String
  inner = concat <$> while (satisfy (/= '"')) (escape stringEscapeSeqs <|> ((:[]) <$> consume))

reservedIds = ["read", "in", "if", "then", "else", "using", "type", "interface", "instance", "cases", "case", "of", "where", "do", "forall", "let", "operator", "switch", "rec"]
reservedCons = ["Type", "Constraint", "Share", "Op"]
reservedOps = [":", "=>", "=", "\\", "->", "@", "&", "?"]

-- Possibly qualified, possibly reserved conid / varid / consym / varsym
stuff :: Tokeniser Token
stuff = form <$> stuff' where
  stuff' = ((:[]) <$> varid) <|> ((:[]) <$> sym) <|> qualified
  varid = satisfy isLower *> while (satisfy isLetter) consume
  conid = satisfy isUpper *> while (satisfy isLetter) consume
  sym = satisfy isSymbol *> while (satisfy isSymbol) consume
  qualified = (:) <$> conid <*> ((satisfies 2 (\[x, y] -> x == '.' && (isLower y || isUpper y || isSymbol y)) *> consume *> stuff') <|> pure [])
  form :: [String] -> Token
  form [x] | x `elem` reservedIds = ReservedId x
           | x `elem` reservedCons = ReservedCon x
           | x `elem` reservedOps = ReservedOp x
  form xs = let qs = Qualified { qualification = init xs, unqualify = last xs } in case last xs of
    x | isLower (head x) -> QVarId qs
    x | isUpper (head x) -> QConId qs
    x | head x == ':'    -> QConSym qs
    _                    -> QVarSym qs
