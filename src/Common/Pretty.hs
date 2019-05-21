{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Common.Pretty
  ( Pretty(..)
  , plain
  , separate
  , module Data.Monoid.Colorful
  ) where

import           Data.Monoid.Colorful

class Pretty a where
  pretty :: a -> Colored String

plain :: String -> Colored String
plain = Value

instance Pretty (Colored String) where
  pretty = id

instance Pretty Char where -- TODO remove this
  pretty = plain . show

separate :: Pretty a => String -> [a] -> Colored String
separate _ []     = Nil
separate _ [x]    = pretty x
separate c (x:xs) = pretty x <> plain c <> separate c xs
