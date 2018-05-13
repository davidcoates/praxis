module Tag
  ( Tag(..)
  , Tagged
  , rec
  , tag
  , value
  , TagTraversable(..)
  ) where

import Data.Bifunctor
import Control.Applicative
import Data.Functor.Identity

data Tag a b = a :< b

type Tagged a b = Tag a (b (Tag a))

rec :: (a -> b -> c) -> Tag a b -> c
rec f (a :< x) = f a x

tag :: Tag a b -> a
tag (a :< x) = a

value :: Tag a b -> b
value (a :< x) = x

instance Eq b => Eq (Tag a b) where
  (_ :< a) == (_ :< b) = a == b

instance Bifunctor Tag where
  bimap f g (a :< x) = f a :< g x

instance Functor (Tag a) where
  fmap = second

instance Monoid a => Applicative (Tag a) where
  pure x = mempty :< x
  liftA2 f (a :< x) (b :< y) = mappend a b :< f x y

-- Map over all the tags in an AST
class TagTraversable c where

  tagTraverse :: Applicative f => (a -> f b) -> Tagged a c -> f (Tagged b c)
  tagTraverse f (a :< x) = liftA2 (:<) (f a) (tagTraverse' f x)
  tagTraverse' :: Applicative f => (a -> f b) -> c (Tag a) -> f (c (Tag b))

  tagMap :: (a -> b) -> Tagged a c -> Tagged b c
  tagMap f = runIdentity . tagTraverse (Identity . f)

  tagFoldMap :: Monoid m => (a -> m) -> Tagged a c -> m
  tagFoldMap f = getConst . tagTraverse (Const . f)

