module Parse.Parse.Parser
  ( Parser(..)
  , runParser
  , satisfy
  , try
  , lookAhead
  , (<?>)
  ) where

import qualified Parse.Prim as Prim
import qualified Parse.Tokenise.Token as Token
import Parse.Parse.AST
import Tag
import Source

import Control.Applicative (Applicative(..), Alternative(..))
import Control.Arrow (left)

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

runParser :: Parser a -> [Token] -> Either String (Tag Source a)
runParser (Parser p) ts = left show $ Prim.runParser (p Prim.<?> info) ts
  where info :: [Token] -> [Token] -> String
        info es es' = "Syntax error " ++ case take (length es - length es') es of {
      [] -> if null ts then "at end of file" else "" ;
      ts -> "on " ++ show ts ++ " starting at " ++ show (start (tag (head ts)))
  }

satisfy :: (Token.Token -> Bool) -> Parser Token.Token
satisfy f = Parser $ Prim.satisfy (f . value)

try :: Parser a -> Parser a
try = lift Prim.try

lookAhead :: Parser a -> Parser a
lookAhead = lift Prim.lookAhead

infix 0 <?>
(<?>) :: Parser a -> String -> Parser a
Parser p <?> s = Parser (p Prim.<?> (\_ _ -> s))

