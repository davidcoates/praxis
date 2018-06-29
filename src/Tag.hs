{-# LANGUAGE FlexibleInstances #-}

module Tag
  ( Tag(..)
  , Tagged
  , rec
  , tag
  , value
  , TagTraversable(..)
  , showable
  ) where

import Control.Applicative
import Data.Bifunctor
import Data.Functor.Identity
import Data.Monoid ((<>))

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
  liftA2 f (a :< x) (b :< y) = (a <> b) :< f x y

-- Map over all the tags in an AST
class TagTraversable c where

  tagTraverse :: Applicative f => (a -> f b) -> Tagged a c -> f (Tagged b c)
  tagTraverse f (a :< x) = liftA2 (:<) (f a) (tagTraverse' f x)
  tagTraverse' :: Applicative f => (a -> f b) -> c (Tag a) -> f (c (Tag b))

  tagMap :: (a -> b) -> Tagged a c -> Tagged b c
  tagMap f = runIdentity . tagTraverse (Identity . f)

  tagFoldMap :: Monoid m => (a -> m) -> Tagged a c -> m
  tagFoldMap f = getConst . tagTraverse (Const . f)

newtype Showable a = Showable a

instance Show a => Show (Showable a) where
  show (Showable x) = show x

instance (Show a, Show b) => Show (Tag (Showable a) b) where
  show (a :< b) = show a ++ " :< " ++ show b

showable :: Tag a b -> Tag (Showable a) b
showable (a :< b) = Showable a :< b
