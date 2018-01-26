module Parse.Tokenise.Tokeniser
  ( Tokeniser(..)
  , runTokeniser
  , satisfy
  , try
  , lookAhead
  , (<?>)
  ) where

import qualified Parse.Prim as Prim
import Parse.Prim (Error(..))
import Source

import Control.Applicative (Applicative(..), Alternative(..))
import Control.Arrow (left)
import Data.List (intercalate)

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
  Tokeniser a >>= f = Tokeniser (a >>= (\x -> attachSource x <$> _runTokeniser (f (value x))))
    where attachSource x x' = Sourced { source = mappend (source x) (source x'), value = value x' }

runTokeniser :: Tokeniser a -> [Sourced Char] -> Either String [Sourced a]
runTokeniser (Tokeniser p) cs = left showE $ Prim.runParser (all p) cs
  where all p = (Prim.eof *> pure []) <|> liftA2 (:) (p Prim.<?> info) (all p)
        info ts ts' = "Lexical error " ++ case take (length ts - length ts') ts of {
      [] -> if null ts then "at end of file" else "" ;
      cs -> "on " ++ formatSpelling (map value cs) ++ " starting at " ++ show (start (source (head cs)))
  }

showE :: Error -> String
showE (Option xs) = concatMap showE xs
showE (Head s e) = s ++ "\n" ++ indent (showE e)
  where indent s = unlines (map ("    " ++) (lines s))

satisfy :: (Char -> Bool) -> Tokeniser Char
satisfy f = Tokeniser $ Prim.satisfy (f . value)

try :: Tokeniser a -> Tokeniser a
try = lift Prim.try

lookAhead :: Tokeniser a -> Tokeniser a
lookAhead = lift Prim.lookAhead

infix 0 <?>
(<?>) :: Tokeniser a -> String -> Tokeniser a
Tokeniser p <?> s = Tokeniser (p Prim.<?> (\_ _ -> s))

