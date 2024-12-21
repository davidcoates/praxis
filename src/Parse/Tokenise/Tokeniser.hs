{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StandaloneDeriving #-}

module Parse.Tokenise.Tokeniser
  ( Tokeniser
  , expected
  , lookahead
  , match
  , run
  ) where

import           Common
import           Parse.Parser        (Parser (..))
import qualified Parse.Parser        as Parser (expected, lookahead, match, run)
import           Praxis              (Praxis, throw, throwAt)
import           Token

import           Control.Applicative (Alternative (..), Applicative (..))
import           Data.Char.WCWidth   (wcwidth)

newtype Tokeniser a = Tokeniser { runTokeniser :: Parser (Sourced Char) (Sourced a) }

instance Functor Tokeniser where
  fmap f (Tokeniser t) = Tokeniser (fmap (fmap f) t)

instance Applicative Tokeniser where
  pure x = Tokeniser $ pure (pure x)
  (<*>) (Tokeniser s) (Tokeniser t) = Tokeniser $ (fmap (<*>) s) <*> t

instance Alternative Tokeniser where
  empty = Tokeniser empty
  Tokeniser a <|> Tokeniser b = Tokeniser (a <|> b)

expected :: String -> Tokeniser a
expected msg = Tokeniser (Parser.expected msg)

lookahead :: Tokeniser a -> Tokeniser a
lookahead = Tokeniser . Parser.lookahead . runTokeniser

match :: (Char -> Bool) -> Tokeniser Char
match p = Tokeniser $ Parser.match (p . view value)

run :: Pretty a => Tokeniser (Maybe a) -> String -> Praxis [Sourced a]
run (Tokeniser t) cs = all (sourced cs) where
  all [] = pure []
  all cs = case Parser.run t cs of
    (Left e, []) -> throw $ "expected " <> pretty e <> " but found EOF"
    (Left e, (s :< t):_) -> throwAt s $ "expected " <> pretty e <> " but found '" <> pretty t <> "'"
    (Right (s :< Just x), cs) -> ((:) <$> pure (s :< x) <*> all cs)
    (Right _, cs) -> all cs

sourced :: String -> [Sourced Char]
sourced = sourced' Pos { line = 1, column = 1 } where
  sourced' _ [] = []
  sourced' start (c:cs) = let end = (advance c start) in (Source start end :< c) : sourced' end cs
  advance :: Char -> Pos -> Pos
  advance c p = case c of
    '\t' -> p { column = tabStop (column p) } where tabStop = (+ 1) . (* 8) . (+ 1) . (`div` 8) . subtract 1
    '\n' -> Pos { line = line p + 1, column = 1 }
    _    -> p { column = column p + wcwidth c }
