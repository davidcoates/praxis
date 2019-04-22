module Syntax.Prism
  ( Prism(..)
  , lift
  ) where

data Prism a b = Prism { construct :: b -> a, destruct :: a -> Maybe b }

lift :: Traversable t => Prism a b -> Prism (t a) (t b)
lift f = Prism (fmap (construct f)) (traverse (destruct f))

