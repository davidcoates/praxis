module Effect
  ( Effect(..)
  , Effects
  , empty
  , unions
  , singleton
  , toList
  , fromList
  ) where

import           Data.List (intercalate)
import           Data.Set  (Set, elems)
import qualified Data.Set  as Set

{-|
  Effects functions as a *flat set* of effect.
  An effect unification variable can be replaced with a flat set of effects, e.g.,
  { EfUni α, EfLit "Read IO" } if α ~> { EfLit "WriteIO", EfLit "ReadHeap" } then the result is { EfLit "WriteIO", EfLit "ReadHeap", EfLit "Read IO" }
-}
data Effect = EfUni String           -- ^An effect unification variable
            | EfLit String           -- ^A concrete effect e.g., Eg `ReadIO`
            | EfVar String           -- ^An effect variable (e.g., e in forall a b e. (a -> b # e) -> [a] -> [b] # e)
            deriving (Ord, Eq)

instance Show Effect where
  show (EfLit s) = s
  show (EfUni s) = s
  show (EfVar s) = s

newtype Effects = Effects { getEffects :: Set Effect }
  deriving (Ord, Eq)

instance Show Effects where
  show (Effects es) = "{" ++ intercalate ", " (map show (elems es)) ++ "}"

empty :: Effects
empty = Effects Set.empty

unions :: [Effects] -> Effects
unions = Effects . Set.unions . map getEffects

singleton :: Effect -> Effects
singleton = Effects . Set.singleton

toList :: Effects -> [Effect]
toList = Set.toList . getEffects

fromList :: [Effect] -> Effects
fromList = Effects . Set.fromList
