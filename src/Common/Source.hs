module Common.Source
  ( Pos(..)
  , Source(..)
  , (<>)
  , Sourced
  ) where

import           Common.Tag

import           Data.Monoid    (Monoid (..))
import           Data.Semigroup (Semigroup (..))

data Pos = Pos { line :: Int, column :: Int } deriving (Eq, Ord)

data Source = Phantom -- ^Used for phantom tokens e.g., implicit whitespace tokens
            | Source { start :: Pos, end :: Pos }
  deriving (Eq, Ord)

instance Show Pos where
  show p = show (line p) ++ ":" ++ show (column p)

instance Show Source where
  show = \case
    Source { start = start } -> show start

-- TODO this is partial
instance Semigroup Source where
  Phantom <> s = s
  s <> Phantom = s
  s <> t       = Source { start = start s, end = end t }

instance Monoid Source where
  mempty = Phantom

type Sourced a = Tag Source a
