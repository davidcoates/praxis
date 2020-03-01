{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Pretty
  ( Option(..)
  , Printable(..)
  , blank
  , Pretty(..)
  , cmap
  , quote
  , separate
  , module Data.Monoid.Colorful
  ) where

import           Common

import           Data.Monoid.Colorful hiding (Pair)
import           Data.String          (IsString (..))

data Option = Plain | Types | Kinds deriving Eq

newtype Printable a = Printable { runPrintable :: Option -> Colored a }

instance Eq a => Eq (Printable a) where
  -- Printable p == Printable q = p Plain == q Plain && p Types == p Types && p Kinds == p Kinds
  (==) = undefined
-- TODO only needed for Token Eq, not actually used...

instance IsString (Printable String) where
  fromString = pure

blank = Printable (const Nil)

instance Semigroup (Printable a) where
  Printable p <> Printable q = Printable (\o -> p o <> q o)

instance Monoid (Printable a) where
  mempty = blank

instance Functor Printable where
  fmap f (Printable p) =  Printable (\o -> f <$> p o)

instance Applicative Printable where
  pure = Printable . const . Value
  liftA2 f (Printable p) (Printable q) = Printable $ \o -> liftA2 f (p o) (q o)

class Pretty a where
  pretty :: a -> Printable String
  prettyIf :: Option -> a -> Printable String
  prettyIf s x = Printable (\t -> if s == t then runPrintable (pretty x) t else Nil)

instance Pretty String where
  pretty = pure

instance Pretty (Colored String) where
  pretty = Printable . const

instance Pretty (Printable String) where
  pretty = id

cmap :: (Colored String -> Colored String) -> Printable String -> Printable String
cmap f (Printable p) = Printable (\o -> f (p o))

quote :: Printable String -> Printable String
quote = cmap (\s -> Style Bold ("'" <> s <> "'"))

separate :: Pretty a => String -> [a] -> Printable String
separate _ []     = blank
separate _ [x]    = pretty x
separate c (x:xs) = pretty x <> pure c <> separate c xs
