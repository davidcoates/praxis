module Parse.Tokenise.Tokeniser
  ( Tokeniser(..)
  , runTokeniser
  , token
  , satisfy
  , try
  , lookAhead
  , (<?>)
  , (<|?>)
  ) where

import qualified Parse.Prim as Prim
import Source
import Tag
import Parse.Tokenise.Token
import Error (Error(..))

import Control.Applicative (Applicative(..), Alternative(..))
import Data.List (intercalate)

newtype Tokeniser a = Tokeniser { _runTokeniser :: Prim.Parser (Annotated Char) (Annotated a) }

lift f (Tokeniser a) = Tokeniser (f a)

instance Functor Tokeniser where
  fmap f = lift (fmap (fmap f))

instance Applicative Tokeniser where
  pure x = Tokeniser (pure (pure x))
  liftA2 f (Tokeniser a) (Tokeniser b) = Tokeniser (liftA2 (liftA2 f) a b)

instance Alternative Tokeniser where
  empty = Tokeniser empty
  Tokeniser a <|> Tokeniser b = Tokeniser (a <|> b)

instance Monad Tokeniser where
  Tokeniser a >>= f = Tokeniser (a >>= \(a :< x) -> liftA2 (\_ y -> y) (a :< x) <$> _runTokeniser (f x))

runTokeniser :: Tokeniser a -> String -> Either Error [Annotated a]
runTokeniser (Tokeniser p) cs = makeError $ Prim.runParser (all p) (sourced cs) tag
  where all p = (Prim.eof *> pure []) <|> liftA2 (:) p (all p)
        makeError (Left (s, e)) = Left $ LexicalError s e
        makeError (Right x)    = Right x

sourced :: String -> [Annotated Char]
sourced = sourced' Pos { line = 1, column = 1 }
  where sourced' _     [] = []
        sourced' p (c:cs) = let p' = advance c p in make p c : sourced' p' cs
        make p c = Source { start = p, end = p, spelling = [c] } :< c

        advance :: Char -> Pos -> Pos
        advance '\t' p = p { column = math (column p) }
          where math = (+ 1) . (* 8) . (+ 1) . (`div` 8) . subtract 1
        advance '\n' p = Pos { line = line p + 1, column = 1 }
        advance _    p = p { column = column p + 1 }

token :: (Char -> Maybe a) -> Tokeniser a
token f = Tokeniser $ Prim.token (lift . fmap f)
  where lift (a :< Just x) = Just (a :< x)
        lift _             = Nothing

satisfy :: (Char -> Bool) -> Tokeniser Char
satisfy f = Tokeniser $ Prim.satisfy (f . value)

try :: Tokeniser a -> Tokeniser a
try = lift Prim.try

lookAhead :: Tokeniser a -> Tokeniser a
lookAhead = lift Prim.lookAhead

infix 0 <?>
(<?>) :: Tokeniser a -> String -> Tokeniser a
Tokeniser p <?> s = Tokeniser (p Prim.<?> s)

infix 0 <|?>
(<|?>) :: Tokeniser a -> String -> Tokeniser a
Tokeniser p <|?> s = Tokeniser (p Prim.<|?> s)
