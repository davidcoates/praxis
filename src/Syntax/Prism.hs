module Syntax.Prism
  ( Prism(..)
  , lift
  , iso
  ) where

import           Data.Maybe (fromJust)
import           Data.Tuple (swap)

data Prism a b = Prism { construct :: b -> a, destruct :: a -> Maybe b }

lift :: Traversable t => Prism a b -> Prism (t a) (t b)
lift f = Prism (fmap (construct f)) (traverse (destruct f))

iso :: (Eq a, Eq b) => [(a, b)] -> Prism a b
iso xs = Prism f g where
  f = fromJust . (`lookup` map swap xs)
  g = Just . fromJust . (`lookup` xs)
