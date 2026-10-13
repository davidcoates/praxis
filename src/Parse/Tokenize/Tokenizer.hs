module Parse.Tokenize.Tokenizer
  ( Tokenizer
  , expected
  , lookahead
  , match
  , run
  ) where

import           Common
import           Parse.Parser        (Parser (..))
import qualified Parse.Parser        as Parser (expected, lookahead, match, run)
import           Praxis              (Praxis, throw, throwAt)
import           Stage
import           Token

import           Control.Applicative (Alternative (..), Applicative (..))
import           Data.Char.WCWidth   (wcwidth)


newtype Tokenizer a = Tokenizer { runTokenizer :: Parser (Sourced Char) (Sourced a) }

instance Functor Tokenizer where
  fmap f (Tokenizer t) = Tokenizer (fmap (fmap f) t)

instance Applicative Tokenizer where
  pure x = Tokenizer $ pure (pure x)
  (<*>) (Tokenizer s) (Tokenizer t) = Tokenizer $ (fmap (<*>) s) <*> t

instance Alternative Tokenizer where
  empty = Tokenizer empty
  Tokenizer a <|> Tokenizer b = Tokenizer (a <|> b)

expected :: String -> Tokenizer a
expected msg = Tokenizer (Parser.expected msg)

lookahead :: Tokenizer a -> Tokenizer a
lookahead = Tokenizer . Parser.lookahead . runTokenizer

match :: (Char -> Bool) -> Tokenizer Char
match p = Tokenizer $ Parser.match (p . view value)

-- | The tokenizer is given the token directly before it (Nothing if there is whitespace in between).
run :: Pretty a => (Maybe a -> Tokenizer (Maybe a)) -> String -> Praxis [Sourced a]
run tokenizer cs = all Nothing (sourced cs) where
  all _ [] = pure []
  all prev cs = case Parser.run (runTokenizer (tokenizer prev)) cs of
    (Left e, []) -> throw Parse $ "expected " <> pretty e <> " but found EOF"
    (Left e, (s :< t):_) -> throwAt Parse s $ "expected " <> pretty e <> " but found '" <> pretty t <> "'"
    (Right (s :< Just x), cs) -> ((:) <$> pure (s :< x) <*> all (Just x) cs)
    (Right _, cs) -> all Nothing cs

sourced :: String -> [Sourced Char]
sourced = sourced' Pos { line = 1, column = 1 } where
  sourced' _ [] = []
  sourced' start (c:cs) = let end = (advance c start) in (Source start end :< c) : sourced' end cs
  advance :: Char -> Pos -> Pos
  advance c p = case c of
    '\t' -> p { column = tabStop (column p) } where tabStop = (+ 1) . (* 8) . (+ 1) . (`div` 8) . subtract 1
    '\n' -> Pos { line = line p + 1, column = 1 }
    _    -> p { column = column p + wcwidth c }
