module Common.Source
  ( Pos(..)
  , Source(..)
  , (<>)
  ) where

import           Data.Monoid    (Monoid (..))
import           Data.Semigroup (Semigroup (..))

data Pos = Pos { line :: Int, column :: Int }

data Source = Source { start :: Pos, end :: Pos, spelling :: String }
            | Phantom -- ^Used for phantom tokens e.g., layout tokens inserted by the tokeniser

instance Show Pos where
  show p = show (line p) ++ ":" ++ show (column p)

instance Show Source where
  show Phantom = "<?>"
  show s       = show (start s) ++ " to " ++ show (end s) ++ " aka {" ++ spelling s ++ "}"

instance Semigroup Source where
  Phantom <> s = s
  s <> Phantom = s
  s1 <> s2     = Source { start = start s1, end = end s2, spelling = spelling s1 ++ spelling s2 }

instance Monoid Source where
  mempty = Phantom
