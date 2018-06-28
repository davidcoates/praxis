module Common
  ( Name
  , asum
  , traverseM
  ) where
-- TODO Where should this be

import Data.Foldable (fold)
import Data.Monoid ((<>))
import Control.Applicative (liftA2)

type Name = String

newtype Special f a b = Special (f (b, a))

instance Functor f => Functor (Special f a) where
  fmap f (Special x) = Special (fmap (\(x, a) -> (f x, a)) x)

instance (Applicative f, Monoid a) => Applicative (Special f a) where
  pure x = Special (pure (x, mempty))
  liftA2 f (Special x) (Special y) = Special $ liftA2 (\(x, a) (y, b) -> (f x y, a <> b)) x y

-- |similar to traverse, but also folds over a monoid
traverseM :: (Monoid c, Applicative f, Traversable t) => (a -> f (b, c)) -> t a -> f (t b, c)
traverseM f as = case traverse (Special . f) as of Special x -> x

-- |Similar to msum but works over an applicative (not to be confused with Data.Foldable.asum)
asum :: (Monoid a, Applicative f, Traversable t) => t (f a) -> f a
asum xs = fold <$> sequenceA xs

