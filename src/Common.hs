{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Common
  ( module Common.Pretty
  , module Common.Source
  , module Common.Tag

  , Name

  , asum
  , series
  , intercalate

  -- |Lenses
  , Lens'
  , makeLenses
  , set
  , view
  , over
  , (.=)
  , (%=)
  , use
  , uses
  , first
  , second

  , Const(..)
  , Identity(..)
  , Sum(..)
  , MaybeT(..)
  , StateT(..)
  , MonadTrans(..)
  , when
  , unless

  , (<&>)

  , PairT(..)

  , Void

  , foldMapA
  ) where

import           Common.Pretty
import           Common.Source
import           Common.Tag

import           Control.Applicative       (Const (..), liftA2)
import           Control.Lens              (Lens', makeLenses, over, set, use,
                                            uses, view, (%=), (.=), _1, _2)
import           Control.Monad             (unless, when)
import           Control.Monad.Trans.Class (MonadTrans (..))
import           Control.Monad.Trans.Maybe (MaybeT (..))
import           Control.Monad.Trans.State (StateT (..))
import           Data.Foldable             (fold)
import           Data.Functor.Identity     (Identity (..))
import           Data.List                 (intercalate)
import           Data.Monoid               (Sum (..))
import           Data.Traversable          (sequenceA)

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

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip (<$>)

-- |Transformer version of ((,) a)
newtype PairT f b a = PairT { runPairT :: f (b, a) }

instance Functor f => Functor (PairT f b) where
  fmap f (PairT x) = PairT (fmap (over second f) x)

data Void

foldMapA :: (Foldable t, Applicative f, Monoid m) => (a -> f m) -> t a -> f m
foldMapA f = foldr (liftA2 mappend . f) (pure mempty)
