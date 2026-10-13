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
  tokens <- signLiterals <$> Tokenizer.run token text
  display Parse "tokens" (separate " " (map (view value) tokens)) `ifFlag` debug
  let tokens' = unlayout topLevel tokens
  display Parse "tokens with layout" (separate " " (map (view value) tokens')) `ifFlag` debug
  return tokens'

-- Helper functions
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
intLiteral = Lit . Integer . read <$> some (match isDigit)

-- | A sign directly before an integer literal is part of the literal, unless the sign directly follows an operand.
-- So @-1@, @(-1)@ and @f -1@ contain the literal -1, but @n-1@ is a subtraction.
signLiterals :: [Sourced Token] -> [Sourced Token]
signLiterals = go Nothing where
  -- The argument is where the previous token ends, if it is an operand.
  go :: Maybe Pos -> [Sourced Token] -> [Sourced Token]
  go operandEnd ((Source s e :< Ident Plain [c]) : (Source s' e' :< Lit (Integer n)) : ts)
    | c `elem` ("+-" :: [Char]), e == s', operandEnd /= Just s
    = go operandEnd ((Source s e' :< Lit (Integer (if c == '-' then negate n else n))) : ts)
  go _ (t : ts) = t : go (operandEndOf t) ts
  go _ [] = []
  operandEndOf (src :< t) = case t of
    Ident _ _   -> Just (end src)
    Lit _       -> Just (end src)
    Special ')' -> Just (end src)
    _           -> Nothing

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
