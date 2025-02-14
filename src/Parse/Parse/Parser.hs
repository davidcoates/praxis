{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}

module Parse.Parse.Parser
  ( Parser
  , parse
  ) where

import           Common
import           Introspect
import qualified Parse.Parser        as Parser
import           Praxis
import           Stage
import           Syntax.Prism
import qualified Syntax.Syntax       as Syntax
import           Syntax.Syntax       (Syntax, SyntaxT)
import           Syntax.Term
import           Term
import           Token

import           Control.Applicative (Alternative (..))
import           Data.Maybe          (fromJust, isJust)


newtype Parser a = Parser { runParser :: Parser.Parser (Sourced Token) (Sourced a) }

instance Syntax Parser where
  f <$> Parser p = Parser ((construct f <$>) <$> p)
  Parser p <*> Parser q = Parser (liftA2 (,) <$> p <*> q)
  empty = Parser empty
  Parser p <|> Parser q = Parser (p <|> q)
  pure = Parser . pure . pure
  match f _ = Parser (over value (fromJust . f) <$> Parser.match (\(_ :< t) -> isJust (f t)))
  expected = Parser . Parser.expected
  internal = const (Parser empty)

instance SyntaxT Parser Initial where
  annotated (Parser p) = Parser ((\(s :< x) -> s :< ((s, ()) :< x)) <$> p)
  blank _ _ = Syntax.pure ()

run :: Pretty a => Parser a -> [Sourced Token] -> Praxis a
run (Parser p) ts = case Parser.run (view value <$> p) ts of
  (Left e, []) -> throw Parse $ "expected " <> pretty e <> " but found EOF"
  (Left e, (s :< t):_) -> throwAt Parse s $ "expected " <> pretty e <> " but found '" <> pretty t <> "'"
  (Right x, ((s :< t):_)) -> throwAt Parse s $ "unexpected " <> pretty t
  (Right x, []) -> return x

parse :: forall a. (IsTerm a, Pretty (Annotated Initial a)) => [Sourced Token] -> Praxis (Annotated Initial a)
parse = run (Syntax.annotated (syntax (termT :: TermT a)))
