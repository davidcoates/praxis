{-# LANGUAGE TemplateHaskell #-}

module Parse.Parser
  ( Parser
  , Alternative(..)
  , Error(..)
  , expected
  , lookahead
  , match
  , run
  ) where

import           Common

import           Control.Applicative (Alternative (..))
import           Control.Arrow       (right)
import           Control.Lens        (makeLenses)
import           Data.Maybe          (fromMaybe)


data Error = Expected String
           | Skip

instance Pretty Error where
  pretty (Expected err) = pretty err
  pretty Skip           = "<unknown>"

data Result t a = Result { _result :: Either Error a, _remaining :: [t], _consumed :: Bool }
makeLenses ''Result

newtype Parser t a = Parser { runParser :: [t] -> Result t a }

instance Functor (Parser t) where
  fmap f p = Parser $ \ts -> over result (right f) (runParser p ts)

instance Applicative (Parser t) where
  pure x = Parser $ \ts -> Result (Right x) ts False
  (<*>) p q = Parser $ \ts -> let r = runParser p ts in case view result r of
    Left  e -> set result (Left e) r -- Same value as r, but with the correct type
    Right f -> let r' = runParser q (view remaining r) in over consumed (|| view consumed r) $ over result (right (\q -> f q)) r'

instance Alternative (Parser t) where
  empty = Parser $ \ts -> Result (Left Skip) ts False
  (<|>) a b = Parser $ \ts -> let r = runParser a ts in case view result r of
    Left  e -> if view consumed r then set result (Left e) r else runParser b ts
    Right _ -> r

expected :: String -> Parser t a
expected msg = Parser $ \ts -> Result (Left (Expected msg)) ts False where

lookahead :: Parser t a -> Parser t a
lookahead p = Parser $ \ts -> let r = runParser p ts in r { _remaining = ts, _consumed = False }

match :: (t -> Bool) -> Parser t t
match p = Parser $ \case
  []     -> Result (Left Skip) [] False
  (t:ts) -> if p t then Result (Right t) ts True else Result (Left Skip) (t:ts) False

run :: Parser t a -> [t] -> (Either Error a, [t])
run p ts = let r = runParser p ts in (view result r, view remaining r) where
