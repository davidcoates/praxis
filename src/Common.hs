module Common
  ( module Common.Pretty
  , module Common.Source
  , module Common.Tag

  , Unique(..)
  , Name(..)
  , mkName
  , nameString
  , I8
  , I16
  , I32
  , I64
  , ISize
  , U8
  , U16
  , U32
  , U64
  , USize

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
  , modifyM
  , save
  , saveLift
  , MonadState
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

  , fold
  , foldMapA

  , isDistinct
  ) where

import           Common.Pretty
import           Common.Source
import           Common.Tag

import qualified Data.Monoid.Colorful       as Colored

import           Control.Applicative        (Const (..), liftA2)
import           Control.Lens               (Lens', _1, _2, both, makeLenses,
                                             over, set, use, uses, view, (%=),
                                             (.=))
import           Control.Monad              (unless, when)
import           Control.Monad.State.Class  (MonadState)
import           Control.Monad.Trans.Class  (MonadTrans (..))
import           Control.Monad.Trans.Except (ExceptT (..), runExceptT)
import           Control.Monad.Trans.State  (StateT (..))
import           Data.Foldable              (fold)
import           Data.Functor.Identity      (Identity (..))
import           Data.Int
import           Data.List                  (intercalate, intersperse, nub)
import           Data.Traversable           (sequenceA)
import           Data.Word

newtype Unique = Unique Int deriving (Eq, Ord, Show)

data Name = Name String Unique deriving (Eq, Ord)

instance Show Name where
  show (Name s _) = s

instance Pretty Name where
  pretty (Name s _) = Colored.Value s

mkName :: String -> Name
mkName s = Name s (Unique 0)

nameString :: Name -> String
nameString (Name s _) = s

type I8    = Int8
type I16   = Int16
type I32   = Int32
type I64   = Int64
type ISize = Int64
type U8    = Word8
type U16   = Word16
type U32   = Word32
type U64   = Word64
type USize = Word64


-- | asum is similar to msum but works over an applicative (not to be confused with Data.Foldable.asum)
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

-- | Transformer version of ((,) a)
newtype PairT f b a = PairT { runPairT :: f (b, a) }

instance Functor f => Functor (PairT f b) where
  fmap f (PairT x) = PairT (fmap (over second f) x)

foldMapA :: (Foldable t, Applicative f, Monoid m) => (a -> f m) -> t a -> f m
foldMapA f = foldr (liftA2 mappend . f) (pure mempty)

just :: Functor f => (a -> f b) -> Maybe a -> f (Maybe b)
just f (Just x) = Just <$> f x

save :: MonadState s m => Lens' s a -> m b -> m b
save l c = do
  x <- use l
  r <- c
  l .= x
  return r

saveLift :: (MonadTrans t, MonadState s m, Monad (t m)) => Lens' s a -> t m b -> t m b
saveLift l c = do
  x <- lift $ use l
  r <- c
  lift $ l .= x
  return r

modifyM :: MonadState s m => Lens' s a -> (a -> m a) -> m ()
modifyM l f = use l >>= f >>= (l .=)

isDistinct :: Eq a => [a] -> Bool
isDistinct xs = length (nub xs) == length xs
