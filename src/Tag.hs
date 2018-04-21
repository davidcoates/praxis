module Tag
  ( Tag(..)
  , Tagged
  , rec
  , tmap
  , tag
  , value
  ) where

import Data.Bifunctor
import Control.Applicative

data Tag a b = a :< b

type Tagged a b = Tag a (b (Tag a))

rec :: (a -> b -> c) -> Tag a b -> c
rec f (a :< x) = f a x

tag :: Tag a b -> a
tag (a :< x) = a

value :: Tag a b -> b
value (a :< x) = x

instance Bifunctor Tag where
  bimap f g (a :< x) = f a :< g x

tmap :: (a -> b) -> Tag a c -> Tag b c
tmap = first

instance Functor (Tag a) where
  fmap = second

instance Monoid a => Applicative (Tag a) where
  pure x = mempty :< x
  liftA2 f (a :< x) (b :< y) = mappend a b :< f x y
