{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE StandaloneDeriving #-}

module Parse.Tokenise.Tokeniser
  ( Tokeniser
  , run
  , consume
  , satisfy
  , satisfies
  , match
  , matches
  , throw
  ) where

import           Common
import           Parse.Parser        (Parser (..))
import qualified Parse.Parser        as Parser (match, run, satisfies, throw)
import           Praxis              (Praxis)
import qualified Praxis              (throw)
import           Token

import           Control.Applicative (Alternative (..), Applicative (..))

newtype Tokeniser a = Tokeniser { runTokeniser :: Parser (Sourced Char) (Sourced a) }

instance Functor Tokeniser where
  fmap f (Tokeniser t) = Tokeniser (fmap (fmap f) t)

instance Applicative Tokeniser where
  pure x = Tokeniser $ pure (pure x)
  (<*>) (Tokeniser s) (Tokeniser t) = Tokeniser $ (fmap (<*>) s) <*> t

instance Alternative Tokeniser where
  empty = Tokeniser empty
  Tokeniser a <|> Tokeniser b = Tokeniser (a <|> b)

run :: Show a => Tokeniser (Maybe a) -> String -> Praxis [Sourced a]
run (Tokeniser t) cs = all (sourced cs)
  where all [] = pure []
        all cs = case Parser.run t cs of
          Left e                  -> Praxis.throw $ e
          Right (s :< Just x, cs) -> ((:) <$> pure (s :< x) <*> all cs)
          Right (_, cs)           -> all cs

sourced :: String -> [Sourced Char]
sourced = sourced' Pos { line = 1, column = 1 }
  where sourced' _     [] = []
        sourced' p (c:cs) = make p c : sourced' (advance c p) cs
        make p c = Source { start = p, end = p } :< c
        advance :: Char -> Pos -> Pos
        advance '\t' p = p { column = math (column p) }
          where math = (+ 1) . (* 8) . (+ 1) . (`div` 8) . subtract 1
        advance '\n' p = Pos { line = line p + 1, column = 1 }
        advance _    p = p { column = column p + 1 }

satisfies :: Int -> (String -> Bool) -> Tokeniser ()
satisfies i f = Tokeniser (Parser.satisfies i (f . map (view value)) *> pure (pure ()))

satisfy :: (Char -> Bool) -> Tokeniser ()
satisfy p = satisfies 1 (\[c] -> p c)

matches :: Int -> (String -> Bool) -> Tokeniser String
matches n p = satisfies n p *> consumes n
  where consumes 0 = pure ""
        consumes n = (:) <$> consume <*> consumes (n - 1)

match :: (Char -> Bool) -> Tokeniser Char
match p = Tokeniser $ Parser.match (p . view value)

consume :: Tokeniser Char
consume = match (const True)

throw :: String -> Tokeniser a
throw = Tokeniser . Parser.throw
