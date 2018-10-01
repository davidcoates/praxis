{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE UndecidableInstances   #-}

module Common
  ( Name
  , asum
  , series
  , PseudoTraversable(..)
  , SemiTraversable(..)
  , extract
  , Substitutable(..)
  , subs
  ) where

import           Control.Applicative   (Const (..), liftA2)
import           Data.Foldable         (fold)
import           Data.Functor.Identity (Identity (..))
import           Data.Monoid           ((<>))
import           Data.Traversable      (sequenceA)

type Name = String

-- |Similar to msum but works over an applicative (not to be confused with Data.Foldable.asum)
asum :: (Monoid a, Applicative f, Traversable t) => t (f a) -> f a
asum xs = fold <$> series xs

series :: (Applicative f, Traversable t) => t (f a) -> f (t a)
series = sequenceA

class PseudoTraversable a b c d | a b c -> d where
  pseudoTraverse :: Applicative f => (a -> f b) -> c -> f d

type SemiTraversable a b = PseudoTraversable a a b b

semiTraverse :: (Applicative f, SemiTraversable a b) => (a -> f a) -> b -> f b
semiTraverse = pseudoTraverse

extract :: (Monoid b, SemiTraversable a a) => (a -> b) -> a -> b
extract f = getConst . semiTraverse (Const . f)

class Substitutable a b where
  sub :: (a -> Maybe b) -> b -> b

subs :: (Substitutable a b, SemiTraversable b c) => (a -> Maybe b) -> c -> c
subs f = runIdentity . semiTraverse (Identity . sub f)

