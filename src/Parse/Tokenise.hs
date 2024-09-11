module Parse.Tokenise
  ( run
  ) where

import           Common                   hiding (asum)
import           Parse.Tokenise.Tokeniser hiding (run)
import qualified Parse.Tokenise.Tokeniser as Tokeniser (run)
import           Parse.Tokenise.Unlayout
import           Praxis                   hiding (throw)
import           Term                     (Lit (..))
import           Token

import           Control.Applicative      (Alternative (..), Applicative (..))
import           Data.Foldable            (asum)
import           Data.List                (intercalate)
import           Data.Maybe               (fromJust)
import           Prelude                  hiding (until)

run :: Bool -> String -> Praxis [Sourced Token]
run topLevel text = do
  tokens <- Tokeniser.run token text
  display "tokens" (separate " " (map (view value) tokens)) `ifFlag` debug
  let tokens' = unlayout topLevel tokens
  display "tokens with layout" (separate " " (map (view value) tokens')) `ifFlag` debug
  return tokens'

-- Helper functions
until :: Tokeniser a -> Tokeniser b -> Tokeniser [b]
until p t = (p *> pure []) <|> ((:) <$> t <*> until p t)

while :: Tokeniser a -> Tokeniser b -> Tokeniser [b]
while p t = (p *> ((:) <$> t <*> while p t)) <|> pure []

char :: Char -> Tokeniser Char
char c = match (== c)

isSymbol = (`elem` "!#$%&*+/<=>?@\\^|-~:[].")
isLower = (`elem` ['a'..'z'])
isUpper = (`elem` ['A'..'Z'])
isDigit = (`elem` ['0'..'9'])
isSpace = (`elem` " \t")
isAlphaNum c = isLower c || isUpper c || isDigit c
isLetter c = c `elem` "_\'" || isAlphaNum c

token :: Tokeniser (Maybe Token)
token = (whitespace *> pure Nothing) <|> (Just <$> (special <|> literal <|> conId <|> varId <|> varIdRef <|> varIdValue <|> varIdView <|> varSym)) <|> throw "illegal character"

whitespace :: Tokeniser ()
whitespace = newline <|> space <|> comment where
  newline = match (`elem` "\r\n\f") *> pure ()
  space = match isSpace *> pure ()
  comment = satisfies 3 (\[a, b, c] -> a == '-' && b == '-' && not (isSymbol c)) *> until newline consume *> pure ()

special :: Tokeniser Token
special = Special <$> match (`elem` "{}(),`_")

literal :: Tokeniser Token
literal = intLiteral <|> charLiteral <|> stringLiteral

intLiteral :: Tokeniser Token
intLiteral = (satisfy isDigit <|> satisfies 2 (\[sign, digit] -> sign `elem` "-+" && isDigit digit)) *> (Lit . Integer <$> decimal) where
  decimal :: Tokeniser Integer
  decimal = build <$> consume <*> while (satisfy isDigit) consume
  build :: Char -> [Char] -> Integer
  build '+' ns = read ns
  build '-' ns = negate (read ns)
  build n   ns = read (n:ns)

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

reservedIds = ["read", "in", "if", "then", "else", "using", "datatype", "enum", "interface", "instance", "cases", "case", "of", "where", "do", "forall", "let", "operator", "switch", "rec", "boxed", "unboxed", "defer", "seq"]
reservedCons = ["Type", "Constraint", "Ref", "View", "Unit", "Pair", "Fn"]
reservedSyms = [":", "=", "\\", "->", "@"] -- TODO should more of these be "contextual" ?

varId :: Tokeniser Token
varId = (\id -> if id `elem` reservedIds then ReservedId id else VarId id) <$> (satisfy isLower *> while (satisfy isLetter) consume)

varIdRef :: Tokeniser Token
varIdRef = satisfies 2 (\[a, b] -> a == '&' && isLower b) *> consume *> (VarIdRef <$> while (satisfy isLetter) consume)

varIdValue :: Tokeniser Token
varIdValue = satisfies 2 (\[a, b] -> a == '!' && isLower b) *> consume *> (VarIdValue <$> while (satisfy isLetter) consume)

varIdView :: Tokeniser Token
varIdView = satisfies 2 (\[a, b] -> a == '?' && isLower b) *> consume *> (VarIdView <$> while (satisfy isLetter) consume)

varSym :: Tokeniser Token
varSym = (\sym -> if sym `elem` reservedSyms then ReservedSym sym else VarSym sym) <$> (satisfy isSymbol *> while (satisfy isSymbol) consume)

conId :: Tokeniser Token
conId = (\id -> if id `elem` reservedCons then ReservedCon id else ConId id) <$> (satisfy isUpper *> while (satisfy isLetter) consume)
