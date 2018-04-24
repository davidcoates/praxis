module Parse.Parse.Parser
  ( Parser(..)
  , runParser
  , token
  , satisfy
  , try
  , lookAhead
  , (<?>)
  , (<|?>)
  ) where

import qualified Parse.Prim as Prim
import Parse.Prim (ParseError)
import qualified Parse.Tokenise.Token as Token
import Parse.Parse.AST
import Tag
import Source
import Compiler (Error(..))

import Control.Applicative (Applicative(..), Alternative(..))

type Token = Token.Annotated Token.Token

newtype Parser a = Parser { _runParser :: Prim.Parser Token (Tag Source a) }

lift f (Parser a) = Parser (f a)

instance Functor Parser where
  fmap f = lift (fmap (fmap f))

instance Applicative Parser where
  pure x = Parser (pure (pure x))
  liftA2 f (Parser a) (Parser b) = Parser (liftA2 (liftA2 f) a b)

instance Alternative Parser where
  empty = Parser empty
  Parser a <|> Parser b = Parser (a <|> b)

instance Monad Parser where
  Parser a >>= f = Parser (a >>= \x -> _runParser (f (value x)))

runParser :: Parser a -> [Token] -> Either Error (Tag Source a)
runParser (Parser p) ts = makeError $ Prim.runParser p ts
  where makeError (Left e, ts) = Left $ SyntaxError (if null ts then EOF else tag (head ts)) (show e)
        makeError (Right x, _) = Right x

token :: (Token.Token -> Maybe a) -> Parser a
token f = Parser $ Prim.token (lift . fmap f)
  where lift (a :< Just x) = Just (a :< x)
        lift _             = Nothing

satisfy :: (Token.Token -> Bool) -> Parser Token.Token
satisfy f = Parser $ Prim.satisfy (f . value)

try :: Parser a -> Parser a
try = lift Prim.try

lookAhead :: Parser a -> Parser a
lookAhead = lift Prim.lookAhead

infix 0 <?>
(<?>) :: Parser a -> String -> Parser a
Parser p <?> s = Parser (p Prim.<?> s)

infix 0 <|?>
(<|?>) :: Parser a -> String -> Parser a
Parser p <|?> s = Parser (p Prim.<|?> s)
