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

import           Common
import           Error                (Error (..))
import qualified Parse.Prim           as Prim
import           Parse.Tokenise.Token
import           Praxis               (Praxis, throwError)

import           Control.Applicative  (Alternative (..), Applicative (..))
import           Data.List            (intercalate)

newtype Tokeniser a = Tokeniser { _runTokeniser :: Prim.Parser (Sourced Char) (Sourced a) }

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

runTokeniser :: Tokeniser a -> String -> Praxis [Sourced a]
runTokeniser (Tokeniser p) cs = makeError $ Prim.runParser (all p) (sourced cs) (view tag)
  where all p = (Prim.eof *> pure []) <|> liftA2 (:) p (all p)
        makeError (Left (s, e)) = throwError (LexicalError s e)
        makeError (Right x)     = pure x

sourced :: String -> [Sourced Char]
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
satisfy f = Tokeniser $ Prim.satisfy (f . (view value))

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
