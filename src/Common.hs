{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes        #-}

module Common
  ( module Common.Pretty
  , module Common.Source
  , module Common.Tag

  , Name

  , asum
  , series
  , intercalate
  , intersperse

  -- |Lenses
  , Lens'
  , makeLenses
  , set
  , view
  , over
  , (.=)
  , (%=)
  , (%%=)
  , use
  , uses
  , first
  , second
  , both

  , liftA2
  , Const(..)
  , Identity(..)
  , ExceptT(..)
  , runExceptT
  , StateT(..)
  , MonadTrans(..)
  , when
  , unless
  , just

  , (<&>)

  , PairT(..)

  , Void
  , absurd

  , fold
  , foldMapA

  , Qualified(..)
  , unqualified
  ) where

import           Common.Pretty
import           Common.Source
import           Common.Tag

import           Control.Applicative        (Const (..), liftA2)
import           Control.Lens               (Lens', both, makeLenses, over, set,
                                             use, uses, view, (%=), (.=), _1,
                                             _2)
import           Control.Monad              (unless, when)
import           Control.Monad.State.Class  (MonadState)
import           Control.Monad.Trans.Class  (MonadTrans (..))
import           Control.Monad.Trans.Except (ExceptT (..), runExceptT)
import           Control.Monad.Trans.State  (StateT (..))
import           Data.Foldable              (fold)
import           Data.Functor.Identity      (Identity (..))
import           Data.List                  (intercalate, intersperse)
import           Data.Traversable           (sequenceA)
import           Data.Void                  (Void, absurd)

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

foldMapA :: (Foldable t, Applicative f, Monoid m) => (a -> f m) -> t a -> f m
foldMapA f = foldr (liftA2 mappend . f) (pure mempty)

just :: Functor f => (a -> f b) -> Maybe a -> f (Maybe b)
just f (Just x) = Just <$> f x

data Qualified a = Qualified { qualification :: [Name], unqualify :: a }
  deriving (Eq, Ord)

-- TODO make this general while suppressing quotes for strings
instance Show (Qualified Name) where
  show q = intercalate "." (qualification q ++ [unqualify q])

unqualified :: a -> Qualified a
unqualified x = Qualified { qualification = [], unqualify = x }


(%%=) :: MonadState s m => Lens' s a -> (a -> m a) -> m ()
(%%=) l f = do
  x <- use l
  x' <- f x
  l .= x'

infix 4 %%=
