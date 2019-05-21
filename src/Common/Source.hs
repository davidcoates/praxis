{-# LANGUAGE OverloadedStrings #-}

module Common.Source
  ( Pos(..)
  , Source(..)
  , (<>)
  ) where

import           Common.Pretty

import           Data.Monoid    (Monoid (..))
import           Data.Semigroup (Semigroup (..))

data Pos = Pos { line :: Int, column :: Int } deriving Eq

data Source = Source { start :: Pos, end :: Pos }
            | Phantom -- ^Used for phantom tokens e.g., implicit whitespace tokens
  deriving Eq

instance Pretty Pos where
  pretty p = plain (show (line p)) <> ":" <> plain (show (column p))

instance Pretty Source where
  pretty Phantom = "<?>"
  pretty s       = pretty (start s)

instance Semigroup Source where
  Phantom <> s = s
  s <> Phantom = s
  s <> t       = Source { start = start s, end = end t }

instance Monoid Source where
  mempty = Phantom
