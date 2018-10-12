{-# LANGUAGE FlexibleInstances #-}

module Tag
  ( Tag(..)
  , tag
  , value
  ) where

import           Control.Applicative
import           Data.Bifunctor
import           Data.Monoid         ((<>))

data Tag a b = a :< b

infixr 6 :<

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

tag :: Functor f => (a -> f c) -> Tag a b -> f (Tag c b)
tag f (a :< x) = (:< x) <$> f a

value :: Functor f => (b -> f c) -> Tag a b -> f (Tag a c)
value f (a :< x) = (a :<) <$> f x
