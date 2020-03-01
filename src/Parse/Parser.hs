{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}

module Parse.Parser
  ( Parser
  , Alternative(..)
  , Error(..)
  , eof
  , mark
  , match
  , run
  , satisfies
  , throw
  ) where

import           Common
import           Pretty

import           Control.Applicative (Alternative (..))
import           Control.Arrow       (right)
import           Control.Lens        (makeLenses)
import           Data.Maybe          (fromMaybe)

data Error = Error (Colored String)
           | Skip

instance Pretty Error where
  pretty (Error s) = pretty s
  pretty Skip      = "<unknown>"

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

match :: (t -> Bool) -> Parser t t
match p = Parser $ \case
  []     -> Result (Left Skip) [] False
  (t:ts) -> if p t then Result (Right t) ts True else Result (Left Skip) (t:ts) False

mark :: String -> Parser t a
mark s = Parser $ \ts -> Result (Left (Error ("expected " <> pure s))) ts False

eof :: Parser t ()
eof = Parser $ \ts -> Result (if null ts then Right () else Left Skip) ts False

run :: Parser t a -> [t] -> (Either Error a, [t])
run p ts = let r = runParser p ts in (view result r, view remaining r)

satisfies :: Int -> ([t] -> Bool) -> Parser t ()
satisfies n p = Parser $ \cs -> case takeExact n cs of
  Just ds -> Result (if p ds then Right () else Left Skip) cs False
  Nothing -> Result (Left Skip) cs False

takeExact :: Int -> [a] -> Maybe [a]
takeExact 0      _ = Just []
takeExact n     [] = Nothing
takeExact n (x:xs) = fmap (x:) (takeExact (n - 1) xs)

throw :: String -> Parser t a
throw s = Parser $ \ts -> Result (Left (Error (pure s))) ts True
