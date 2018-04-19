module Parse.Prim
  ( Parser(..)
  , runParser
  , Error(..)
  , eof
  , satisfy
  , try
  , lookAhead
  , many
  , (<?>)
  ) where

import Control.Applicative (Applicative, Alternative, pure, liftA2, empty, (<|>))
import Control.Arrow (left)

data Error = Option [Error]
           | Head String Error

instance Show Error where
  show (Option xs) = concatMap show xs
  show (Head s e) = s ++ "\n" ++ indent (show e)
    where indent s = unlines (map ("    " ++) (lines s))

err :: Either Error b
err = Left (Option [])

-- | Parser takes a list of tokens, and returns a triple of:
-- |  1) Left <error> on parse error, or Right <AST>
-- |  2) List of remaining tokens
-- |  3) Whether or not any tokens were consumed
newtype Parser t a = Parser { _runParser :: [t] -> (Either Error a, [t], Bool) } 

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
  empty = Parser $ \ts -> (err, ts, False)
  a <|> b = Parser $ \ts -> case _runParser a ts of
    (Left e, ts', c) -> if c then (Left e, ts', c) else let (x, y, z) = _runParser b ts' in (left (errApp e) x, y, z)
      where errApp (Head x xs) (Head y ys) = Head (x ++ " | " ++ y) ys
            errApp _           b           = b
    success           -> success

instance Monad (Parser t) where
  a >>= f = Parser $ \ts -> case _runParser a ts of
    (Right x, ts', c) -> let (y, ts'', c') = _runParser (f x) ts' in (y, ts'', c || c')
    (Left e,  ts', c) -> (Left e, ts', c)


runParser :: Parser t a -> [t] -> Either Error a
runParser p ts = let (x,_,_) = _runParser p ts in x

eof :: Parser t ()
eof = Parser $ \ts -> (if null ts then Right () else err, ts, False)

satisfy :: (t -> Bool) -> Parser t t
satisfy f = Parser $ \ts -> case ts of
  []     -> (err, ts, False)
  (t:ts) -> (if f t then Right t else err, ts, True)

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
(<?>) :: Parser t a -> ([t] -> [t] -> String) -> Parser t a
p <?> f = Parser $ \ts -> case _runParser p ts of
  (Left e, ts', c) -> (Left (Head (f ts ts') e), ts', c)
  success          -> success

{-
infix 0 <|?>
(<|?>) :: Parser t a -> ([t] -> [t] -> String) -> Parser t a
p <|?> f = Parser $ \ts -> case _runParser p ts of
  (Left e, ts', False) -> (Left (Head (f ts ts') e), ts', False)
  success              -> success
-}

