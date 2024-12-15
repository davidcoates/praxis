module Parse.Tokenise
  ( run
  ) where

import           Common                   hiding (asum)
import           Parse.Tokenise.Tokeniser hiding (run)
import qualified Parse.Tokenise.Tokeniser as Tokeniser (run)
import           Parse.Tokenise.Unlayout
import           Praxis
import           Term                     (Lit (..))
import           Token

import           Control.Applicative      (Alternative (..), Applicative (..))
import           Data.Foldable            (asum)
import           Data.List                (intercalate)
import           Data.Maybe               (fromJust)

run :: Bool -> String -> Praxis [Sourced Token]
run topLevel text = do
  tokens <- Tokeniser.run token text
  display "tokens" (separate " " (map (view value) tokens)) `ifFlag` debug
  let tokens' = unlayout topLevel tokens
  display "tokens with layout" (separate " " (map (view value) tokens')) `ifFlag` debug
  return tokens'

-- Helper functions
consume :: Tokeniser Char
consume = match (const True)

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
token = (whitespace *> pure Nothing) <|> (Just <$> (special <|> literal <|> conId <|> varId <|> varIdRef <|> varIdValue <|> varIdView <|> varSym)) <|> expected "illegal character"

whitespace :: Tokeniser ()
whitespace = newline <|> space <|> comment where
  newline = match (`elem` "\r\n\f") *> pure ()
  space = match isSpace *> pure ()
  comment = lookahead (char '-' *> char '-' *> match (not . isSymbol)) *> many (match (not . (`elem` "\r\n\f"))) *> pure ()

special :: Tokeniser Token
special = Special <$> match (`elem` "{}(),`_")

literal :: Tokeniser Token
literal = intLiteral <|> charLiteral <|> stringLiteral

intLiteral :: Tokeniser Token
intLiteral = lookahead (match isDigit <|> match (`elem` "-+") *> match isDigit) *> (Lit . Integer <$> decimal) where
  decimal :: Tokeniser Integer
  decimal = build <$> consume <*> many (match isDigit)
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
escape seqs = char '\\' *> (seq <|> expected "invalid escape sequence") where
    seq = (\c -> fromJust (c `lookup` seqs)) <$> match (`elem` map fst seqs)

charLiteral :: Tokeniser Token
charLiteral = char '\'' *> ((Lit . Char <$> inner) <* char '\'' <|> expected "unterminated character literal") where
  inner :: Tokeniser Char
  inner = escape charEscapeSeqs <|> match (/= '\'')

stringLiteral :: Tokeniser Token
stringLiteral = char '"' *> ((Lit . String <$> inner) <* char '"' <|> expected "unterminated string literal") where
  inner :: Tokeniser String
  inner = concat <$> many (escape stringEscapeSeqs <|> ((:[]) <$> match (/= '"')))

reservedIds = ["read", "in", "if", "then", "else", "using", "datatype", "enum", "interface", "instance", "cases", "case", "of", "where", "do", "forall", "let", "operator", "switch", "rec", "boxed", "unboxed", "defer", "seq"]
reservedCons = ["Type", "Constraint", "Ref", "View", "Unit", "Pair", "Fn"]
reservedSyms = [":", "=", "\\", "->", "@"] -- TODO should more of these be "contextual" ?

varId :: Tokeniser Token
varId = (\id -> if id `elem` reservedIds then ReservedId id else VarId id) <$> ((:) <$> match isLower <*> many (match isLetter))

varIdRef :: Tokeniser Token
varIdRef = lookahead (char '&' *> match isLower) *> consume *> (VarIdRef <$> many (match isLetter))

varIdValue :: Tokeniser Token
varIdValue = lookahead (char '!' *> match isLower) *> consume *> (VarIdValue <$> many (match isLetter))

varIdView :: Tokeniser Token
varIdView = lookahead (char '?' *> match isLower) *> consume *> (VarIdView <$> many (match isLetter))

varSym :: Tokeniser Token
varSym = (\sym -> if sym `elem` reservedSyms then ReservedSym sym else VarSym sym) <$> ((:) <$> match isSymbol <*> many (match isSymbol))

conId :: Tokeniser Token
conId = (\id -> if id `elem` reservedCons then ReservedCon id else ConId id) <$> ((:) <$> match isUpper <*> many (match isLetter))
