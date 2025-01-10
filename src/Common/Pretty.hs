{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Common.Pretty
  ( Pretty(..)
  , separate
  , module Data.Monoid.Colorful
  ) where

import           Control.Applicative  (liftA2)
import           Data.Monoid.Colorful (Color (..), Colored, Style (..))
import qualified Data.Monoid.Colorful as Colored
import           Data.String          (IsString (..))

import           Stage


class Pretty a where
  pretty :: a -> Colored String

instance Pretty String where
  pretty = pure

instance Pretty (Colored String) where
  pretty = id

instance Pretty Char where
  pretty = pretty . (:[])

separate :: Pretty a => String -> [a] -> Colored String
separate _ []     = Colored.Nil
separate _ [x]    = pretty x
separate c (x:xs) = pretty x <> pretty c <> separate c xs
