module Parse.Prim
  ( Parser(..)
  , ParseError(..)
  , runParser
  , eof
  , token
  , satisfy
  , try
  , lookAhead
  , many
  , (<?>)
  , (<|?>)
  ) where

import Control.Applicative (Applicative, Alternative, pure, liftA2, empty, (<|>))
import Control.Arrow (left)

data ParseError = Option ParseError ParseError
                | Atom String
                | Generic

instance Show ParseError where
  show e = case toList e of
    []  -> "<unknown>"
    [x] -> "expected " ++ x
    xs  -> "expected one of " ++ show xs
    where toList (Option a b) = toList a ++ toList b
          toList (Atom s)     = [s]
          toList Generic      = []

-- |Parser takes a list of tokens, and returns a triple of:
-- | 1) Left <error> on parse error, or Right <AST>
-- | 2) List of remaining tokens
-- | 3) Whether or not any tokens were consumed
newtype Parser t a = Parser { _runParser :: [t] -> (Either ParseError a, [t], Bool) }

instance Functor (Parser t) where
  fmap f p = Parser $ \ts -> let (x, y, z) = _runParser p ts in (fmap f x, y, z)

instance Applicative (Parser t) where
  pure a = Parser $ \ts -> (pure a, ts, False)
  liftA2 f a b = Parser $ \ts -> case _runParser a ts of
    (Left e, ts', c)  -> (Left e, ts', c)
    (Right x, ts', c) -> case _runParser b ts' of
      (Left e', ts'', c') -> (Left e',       ts'', c || c')
      (Right y, ts'', c') -> (Right (f x y), ts'', c || c')

instance Alternative (Parser t) where
  empty = Parser $ \ts -> (Left Generic, ts, False)
  a <|> b = Parser $ \ts -> case _runParser a ts of
    (Left e, ts', c) -> if c then (Left e, ts', c) else let (x, y, z) = _runParser b ts' in (left (Option e) x, y, z)
    success           -> success

instance Monad (Parser t) where
  a >>= f = Parser $ \ts -> case _runParser a ts of
    (Right x, ts', c) -> let (y, ts'', c') = _runParser (f x) ts' in (y, ts'', c || c')
    (Left e,  ts', c) -> (Left e, ts', c)

runParser :: Parser t a -> [t] -> (Either ParseError a, [t])
runParser p ts = let (x,y,_) = _runParser p ts in (x,y)

eof :: Parser t ()
eof = Parser $ \ts -> (if null ts then Right () else Left Generic, ts, False)

token :: (t -> Maybe a) -> Parser t a
token f = Parser $ \ts -> case ts of
  []     -> (Left Generic, ts, False)
  (t:ts) -> case f t of Just x -> (Right x,      ts, True)
                        _      -> (Left Generic, ts, True)

satisfy :: (t -> Bool) -> Parser t t
satisfy f = token (\t -> if f t then Just t else Nothing)

try :: Parser t a -> Parser t a
try p = Parser $ \ts -> case _runParser p ts of
  (Left e, ts', c) -> (Left e, ts, False)
  success          -> success

lookAhead :: Parser t a -> Parser t a
lookAhead p = Parser $ \ts -> case _runParser p ts of
  (Right x, ts', c) -> (Right x, ts, False)
  failure           -> failure

many :: Parser t a -> Parser t [a]
many p = liftA2 (:) (try p) (many p) <|> pure []

infix 0 <?>
(<?>) :: Parser t a -> String -> Parser t a
p <?> s = Parser $ \ts -> case _runParser p ts of
  (Left _, ts', c) -> (Left (Atom s), ts', c)
  success          -> success

infix 0 <|?>
(<|?>) :: Parser t a -> String -> Parser t a
p <|?> s = Parser $ \ts -> case _runParser p ts of
  (Left e, ts', False) -> (Left (Atom s), ts', False)
  success              -> success
