{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}

module Common.Tag
  ( Tag(..)
  , tag
  , value
  ) where

import           Common.Pretty

import           Control.Applicative
import           Data.Bifunctor
import           Data.Monoid         ((<>))

data Tag a b = a :< b

{-
There is no way to get a <> b :< c to parse as (a <> b) :< c
and simultaenously a :< b : c to parse as (a :< b) : c
(without changing the fixity of <> or :)

I've prefered the second, otherwise this should be 5.
-}
infixl 6 :<

instance Eq b => Eq (Tag a b) where
  (_ :< a) == (_ :< b) = a == b

instance Ord b => Ord (Tag a b) where
  (_ :< a) `compare` (_ :< b) = a `compare` b

instance Bifunctor Tag where
  bimap f g (a :< x) = f a :< g x

instance Functor (Tag a) where
  fmap = second

instance Monoid a => Applicative (Tag a) where
  pure x = mempty :< x
  liftA2 f (a :< x) (b :< y) = (a <> b) :< f x y

instance Foldable (Tag a) where
  foldr f x (a :< y) = f y x

instance Traversable (Tag a) where
  traverse = value

tag :: Functor f => (a -> f c) -> Tag a b -> f (Tag c b)
tag f (a :< x) = (:< x) <$> f a

value :: Functor f => (b -> f c) -> Tag a b -> f (Tag a c)
value f (a :< x) = (a :<) <$> f x

-- TODO this is a hack
instance Pretty (Tag a b) => Show (Tag a b) where
  show x = showColoredS TermDumb (pretty x) ""
