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
import qualified Data.Map.Strict          as Map
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

token :: Maybe Token -> Tokenizer (Maybe Token)
token prev = (whitespace *> pure Nothing) <|> (Just <$> (special <|> literal prev <|> upper <|> lower <|> symbol)) <|> expected "token"

whitespace :: Tokenizer ()
whitespace = newline <|> space <|> comment where
  newline = match isNewline *> pure ()
  space = match isSpace *> pure ()
  comment = lookahead (char '-' *> char '-' *> match (not . isSymbol)) *> many (match (not . isNewline)) *> pure ()

special :: Tokenizer Token
special = Special <$> match (`elem` ("{}(),`_" :: [Char]))

literal :: Maybe Token -> Tokenizer Token
literal prev = intLiteral prev <|> charLiteral <|> stringLiteral

intLiteral :: Maybe Token -> Tokenizer Token
intLiteral prev = lookahead (match isDigit <|> sign *> match isDigit) *> (Lit . Integer <$> decimal) where
  sign = match (\c -> signed && c `elem` ("-+" :: [Char]))
  -- A sign directly after an operand is not part of the literal
  signed = case prev of
    Just (Ident _ _)   -> False
    Just (Lit _)       -> False
    Just (Special ')') -> False
    _                  -> True
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

keywordMap :: Map.Map String Keyword
keywordMap = Map.fromList [ (keywordString kw, kw) | kw <- [minBound..maxBound] ]

toToken :: String -> Token
toToken str = maybe (Ident Plain str) Keyword (Map.lookup str keywordMap)

upper :: Tokenizer Token
upper = toToken <$> ((:) <$> match isUpper <*> many (match isLetter))

lower :: Tokenizer Token
lower =
  toToken <$> lower' <|>
  lookahead (flavor *> match isLower) *> (Ident <$> flavor <*> lower') where
    lower' :: Tokenizer String
    lower' = (:) <$> match isLower <*> many (match isLetter)
    flavor :: Tokenizer Flavor
    flavor =
      char '&' *> pure Ref   <|>
      char '!' *> pure Value <|>
      char '?' *> pure View

symbol :: Tokenizer Token
symbol = toToken <$> some (match isSymbol)
