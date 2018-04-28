module Tag
  ( Tag(..)
  , Tagged
  , rec
  , tag
  , value
  , DeepTagFunctor(..)
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

instance Functor (Tag a) where
  fmap = second

instance Monoid a => Applicative (Tag a) where
  pure x = mempty :< x
  liftA2 f (a :< x) (b :< y) = mappend a b :< f x y

-- Map over all the tags in an AST
class DeepTagFunctor b where
  tmap :: (a -> a) -> Tagged a b -> Tagged a b
  tmap f (a :< x) = f a :< tmap' f x
  tmap' :: (a -> a) -> b (Tag a) -> b (Tag a)
