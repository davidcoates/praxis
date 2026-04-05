module Parse.Tokenize
  ( run
  ) where

import           Common                   hiding (asum)
import           Parse.Tokenize.Tokenizer hiding (run)
import qualified Parse.Tokenize.Tokenizer as Tokenizer (run)
import           Parse.Tokenize.Unlayout
import           Praxis
import           Stage
import           Term                     (Flavor (..), Lit (..))
import           Token

import           Control.Applicative      (Alternative (..), Applicative (..))
import           Data.Foldable            (asum)
import           Data.List                (intercalate)
import           Data.Maybe               (fromJust)

run :: Bool -> String -> Praxis [Sourced Token]
run topLevel text = do
  tokens <- Tokenizer.run token text
  display Parse "tokens" (separate " " (map (view value) tokens)) `ifFlag` debug
  let tokens' = unlayout topLevel tokens
  display Parse "tokens with layout" (separate " " (map (view value) tokens')) `ifFlag` debug
  return tokens'

-- Helper functions
consume :: Tokenizer Char
consume = match (const True)

char :: Char -> Tokenizer Char
char c = match (== c)

isDigit = (`elem` ['0'..'9'])
isSpace = (`elem` (" \t" :: [Char]))
isAlphaNum c = isLower c || isUpper c || isDigit c
isLetter c = c `elem` ("_\'" :: [Char]) || isAlphaNum c
isNewline = (`elem` ("\r\n\f" :: [Char]))

token :: Tokenizer (Maybe Token)
token = (whitespace *> pure Nothing) <|> (Just <$> (special <|> literal <|> upper <|> lower <|> symbol)) <|> expected "token"

whitespace :: Tokenizer ()
whitespace = newline <|> space <|> comment where
  newline = match isNewline *> pure ()
  space = match isSpace *> pure ()
  comment = lookahead (char '-' *> char '-' *> match (not . isSymbol)) *> many (match (not . isNewline)) *> pure ()

special :: Tokenizer Token
special = Special <$> match (`elem` ("{}(),`_" :: [Char]))

literal :: Tokenizer Token
literal = intLiteral <|> charLiteral <|> stringLiteral

intLiteral :: Tokenizer Token
intLiteral = lookahead (match isDigit <|> match (`elem` ("-+" :: [Char])) *> match isDigit) *> (Lit . Integer <$> decimal) where
  decimal :: Tokenizer Integer
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

escape :: [(Char, a)] -> Tokenizer a
escape seqs = char '\\' *> (seq <|> expected "invalid escape sequence") where
    seq = (\c -> fromJust (c `lookup` seqs)) <$> match (`elem` map fst seqs)

charLiteral :: Tokenizer Token
charLiteral = char '\'' *> ((Lit . Char <$> inner) <* char '\'' <|> expected "unterminated character literal") where
  inner :: Tokenizer Char
  inner = escape charEscapeSeqs <|> match (/= '\'')

stringLiteral :: Tokenizer Token
stringLiteral = char '"' *> ((Lit . String <$> inner) <* char '"' <|> expected "unterminated string literal") where
  inner :: Tokenizer String
  inner = concat <$> many (escape stringEscapeSeqs <|> ((:[]) <$> match (/= '"')))

-- TODO should more of these be contextual ?
keywords = [
  "read", "in", "if", "then", "else", "using", "datatype", "enum", "cases", "case", "of", "where", "do", "forall", "let", "operator", "switch", "rec", "defer", "seq",
  "Type", "Constraint", "Clone", "Dispose", "Copy", "Capture", "Integral",
  ":", "=", "\\", "->", "@"]

upper :: Tokenizer Token
upper = (\str -> if str `elem` keywords then Keyword Upper str else Ident Plain Upper str) <$> ((:) <$> match isUpper <*> many (match isLetter))

lower :: Tokenizer Token
lower =
  (\str -> if str `elem` keywords then Keyword Lower str else Ident Plain Lower str) <$> lower' <|>
  lookahead (flavor *> match isLower) *> (Ident <$> flavor <*> pure Lower <*> lower') where
    lower' :: Tokenizer String
    lower' = (:) <$> match isLower <*> many (match isLetter)
    flavor :: Tokenizer Flavor
    flavor =
      char '&' *> pure Ref   <|>
      char '!' *> pure Value <|>
      char '?' *> pure View

symbol :: Tokenizer Token
symbol = (\str -> if str `elem` keywords then Keyword Symbol str else Ident Plain Symbol str) <$> some (match isSymbol)
