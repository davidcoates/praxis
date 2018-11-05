module Common.Misc
  ( Name
  , asum
  , both
  , series
  , set
  , view
  , over
  , (.=)
  , (%=)
  , makeLenses
  , Lens'
  , use
  , first
  , second
  , Const(..)
  , Identity(..)
  ) where

import           Control.Applicative    (Const (..))
import           Data.Foldable          (fold)
import           Data.Functor.Identity  (Identity (..))
import           Data.Traversable       (sequenceA)

import           Control.Lens           (Lens', makeLenses, over, set, use,
                                         view, (%=), (.=), _1, _2)
import           Control.Lens.Traversal (both)

type Name = String

-- |Similar to msum but works over an applicative (not to be confused with Data.Foldable.asum)
asum :: (Monoid a, Applicative f, Traversable t) => t (f a) -> f a
asum xs = fold <$> series xs

series :: (Applicative f, Traversable t) => t (f a) -> f (t a)
series = sequenceA

first :: Functor f => (a -> f b) -> (a, n) -> f (b, n)
first = _1

second :: Functor f => (a -> f b) -> (n, a) -> f (n, b)
second = _2

