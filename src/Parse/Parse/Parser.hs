module Parse.Parse.Parser
  ( Parser(..)
  , runParser
  , token
  , satisfy
  , try
  , lookAhead
  , parsed
  , (<?>)
  , (<|?>)
  ) where

import           Common
import           Error
import           Parse.Annotate
import           Parse.Parse.AST
import qualified Parse.Prim           as Prim
import qualified Parse.Tokenise.Token as Token
import           Praxis               (Praxis, throwError)
import           Stage

import           Control.Applicative  (Alternative (..), Applicative (..))

type Token = Sourced Token.Token

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
  Parser a >>= f = Parser (a >>= \x -> _runParser (f (view value x)))

runParser :: Parser a -> [Token] -> Praxis (Tag (Source, ()) a)
runParser (Parser p) ts = makeError $ Prim.runParser (p <* Prim.eof) ts (view tag) -- TODO eof here breaks error messages
  where makeError (Left (s, e))    = throwError $ SyntaxError (SweetError s e)
        makeError (Right (a :< x)) = pure ((a, ()) :< x)

token :: (Token.Token -> Maybe a) -> Parser a
token f = Parser $ Prim.token (lift . fmap f)
  where lift (a :< Just x) = Just (a :< x)
        lift _             = Nothing

satisfy :: (Token.Token -> Bool) -> Parser Token.Token
satisfy f = Parser $ Prim.satisfy (f . view value)

try :: Parser a -> Parser a
try = lift Prim.try

lookAhead :: Parser a -> Parser a
lookAhead = lift Prim.lookAhead

-- Used to extract annotation
parsed :: Parser a -> Parser (Tag (Source, ()) a)
parsed = lift (fmap (\(a :< x) -> a :< ((a, ()) :< x)))

infix 0 <?>
(<?>) :: Parser a -> String -> Parser a
Parser p <?> s = Parser (p Prim.<?> s)

infix 0 <|?>
(<|?>) :: Parser a -> String -> Parser a
Parser p <|?> s = Parser (p Prim.<|?> s)
