{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Common.Source
  ( Pos(..)
  , Source(..)
  , (<>)
  , Sourced
  ) where

import           Common.Pretty
import           Common.Tag

import           Data.Monoid    (Monoid (..))
import           Data.Semigroup (Semigroup (..))

data Pos = Pos { line :: Int, column :: Int } deriving Eq

data Source = EndOfFile
            | Phantom -- ^Used for phantom tokens e.g., implicit whitespace tokens
            | Source { start :: Pos, end :: Pos }
  deriving Eq

instance Pretty Pos where
  pretty p = plain (show (line p)) <> ":" <> plain (show (column p))

instance Pretty Source where
  pretty = \case
    EndOfFile  -> "eof"
    Phantom    -> "<?>"
    Source s _ -> pretty s

-- TODO this is partial
instance Semigroup Source where
  Phantom <> s = s
  s <> Phantom = s
  s <> t       = Source { start = start s, end = end t }

instance Monoid Source where
  mempty = Phantom

type Sourced a = Tag Source a

instance Pretty a => Pretty (Sourced a) where
  pretty (Phantom :< x) = pretty x
  pretty (a :< x)       = pretty a <> " " <> pretty x
