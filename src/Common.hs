module Common
  ( Name
  , traverseF
  ) where
-- TODO Where should this be

import Data.Monoid ((<>))
import Control.Applicative (liftA2)

type Name = String


newtype Special f a b = Special (f (b, a))

instance Functor f => Functor (Special f a) where
  fmap f (Special x) = Special (fmap (\(x, a) -> (f x, a)) x)

instance (Applicative f, Monoid a) => Applicative (Special f a) where
  pure x = Special (pure (x, mempty))
  liftA2 f (Special x) (Special y) = Special $ liftA2 (\(x, a) (y, b) -> (f x y, a <> b)) x y

traverseF :: (Monoid c, Applicative f, Traversable t) => (a -> f (b, c)) -> t a -> f (t b, c)
traverseF f as = case traverse (Special . f) as of Special x -> x

