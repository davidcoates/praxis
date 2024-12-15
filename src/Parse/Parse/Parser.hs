{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies      #-}

module Parse.Parse.Parser
  ( Parser
  , run
  ) where

import           Common
import qualified Parse.Parser        as Parser
import           Praxis
import qualified Syntax.Parser       as Syntax
import           Term
import           Token

import           Control.Applicative (Alternative (..))

newtype Parser a = Parser { runParser :: Parser.Parser (Sourced Token) (Sourced a) }

instance Functor Parser where
  fmap f (Parser p) = Parser (fmap f <$> p)

instance Applicative Parser where
  pure x = Parser (pure (pure x))
  Parser f <*> Parser p = Parser ((<*>) <$> f <*> p)

instance Alternative Parser where
  empty = Parser empty
  Parser p <|> Parser q = Parser (p <|> q)

instance Syntax.Parser Parser where
  match f = Parser $ Parser.match (f . view value)
  expected = Parser . Parser.expected
  sourced (Parser p) = Parser ((\(s :< x) -> (s :< (s :< x))) <$> p)

run :: Pretty a => Parser a -> [Sourced Token] -> Praxis a
run (Parser p) ts = case Parser.run (view value <$> p) ts of
  (Left e, []) -> throw $ "expected " <> pretty e <> " but found EOF"
  (Left e, (s :< t):_) -> throwAt s $ "expected " <> pretty e <> " but found '" <> pretty t <> "'"
  (Right x, ((s :< t):_)) -> throwAt s $ "unexpected " <> pretty t
  (Right x, []) -> return x
