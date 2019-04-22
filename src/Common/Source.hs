module Common.Source
  ( Pos(..)
  , Source(..)
  , (<>)
  ) where

import           Data.Monoid    (Monoid (..))
import           Data.Semigroup (Semigroup (..))

data Pos = Pos { line :: Int, column :: Int }

data Source = Source { start :: Pos, end :: Pos }
            | Phantom -- ^Used for phantom tokens e.g., implicit whitespace tokens

instance Show Pos where
  show p = show (line p) ++ ":" ++ show (column p)

instance Show Source where
  show Phantom = "<?>"
  show s       = show (start s) -- ++ " to " ++ show (end s)

instance Semigroup Source where
  Phantom <> s = s
  s <> Phantom = s
  s <> t       = Source { start = start s, end = end t }

instance Monoid Source where
  mempty = Phantom
