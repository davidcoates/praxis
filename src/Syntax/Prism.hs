module Syntax.Prism
  ( Prism(..)
  , lift
  ) where


-- | Combination of a covariant and a contravariant function.
-- Parsers use construct, Unparsers use destruct.
data Prism a b = Prism { construct :: b -> a, destruct :: a -> Maybe b }

lift :: Traversable t => Prism a b -> Prism (t a) (t b)
lift f = Prism (fmap (construct f)) (traverse (destruct f))
