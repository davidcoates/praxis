module Common
  ( Name
  , asum
  , series
  ) where
-- TODO Where should this be

import           Control.Applicative (liftA2)
import           Data.Foldable       (fold)
import           Data.Monoid         ((<>))
import           Data.Traversable    (sequenceA)

type Name = String

-- |Similar to msum but works over an applicative (not to be confused with Data.Foldable.asum)
asum :: (Monoid a, Applicative f, Traversable t) => t (f a) -> f a
asum xs = fold <$> series xs

series :: (Applicative f, Traversable t) => t (f a) -> f (t a)
series = sequenceA
