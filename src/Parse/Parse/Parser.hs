module Parse.Parse.Parser
  ( Parser(..)
  , runParser
  , satisfy
  , try
  , lookAhead
  , (<?>)
  ) where

import qualified Parse.Prim as Prim
import Parse.Prim (Error(..))
import Parse.Tokenise.Token (Token, Type)
import Parse.Parse.AST
import Source

import Control.Applicative (Applicative(..), Alternative(..))
import Control.Arrow (left)

newtype Parser a = Parser { _runParser :: Prim.Parser Token a }

lift f (Parser a) = Parser (f a)

instance Functor Parser where
  fmap f = lift (fmap f)

instance Applicative Parser where
  pure x = Parser (pure x)
  liftA2 f (Parser a) (Parser b) = Parser (liftA2 f a b)

instance Alternative Parser where
  empty = Parser empty
  Parser a <|> Parser b = Parser (a <|> b)

instance Monad Parser where
  Parser a >>= f = Parser (a >>= \x -> _runParser (f x))

runParser :: Parser a -> [Token] -> Either String a
runParser (Parser p) ts = left show' $ Prim.runParser (p Prim.<?> info) ts
  where info :: [Token] -> [Token] -> String
        info es es' = "Syntax error " ++ case take (length es - length es') es of {
      [] -> if null ts then "at end of file" else "" ;
      ts -> "on " ++ show ts ++ " starting at " ++ show (start (source (head ts)))
  }

-- TODO make this instance Show Error?
show' :: Error -> String
show' (Option xs) = concatMap show' xs
show' (Head s e) = s ++ "\n" ++ indent (show' e)
  where indent s = unlines (map ("    " ++) (lines s))

satisfy :: (Type -> Bool) -> Parser Token
satisfy f = Parser $ Prim.satisfy (f . value)

try :: Parser a -> Parser a
try = lift Prim.try

lookAhead :: Parser a -> Parser a
lookAhead = lift Prim.lookAhead

infix 0 <?>
(<?>) :: Parser a -> String -> Parser a
Parser p <?> s = Parser (p Prim.<?> (\_ _ -> s))

