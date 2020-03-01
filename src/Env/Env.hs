{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StandaloneDeriving #-}

module Env.Env
  ( Env(..)
  , adjust
  )
where

import           Common
import           Control.Lens (Traversal)
import           Data.List    (intercalate)
import           Env
import           Prelude      hiding (lookup)
import qualified Prelude      (lookup)
import           Pretty

-- TODO Cosider putting source in Env
newtype Env a b = Env [(a, b)]

deriving instance Foldable (Env a)
deriving instance Traversable (Env a)

instance Functor (Env a) where
  fmap f (Env l) = Env (fmap (over second f) l)

instance Environment Env where
  intro a b (Env l) = Env ((a,b):l)
  elim (Env (_:l)) = Env l
  empty = Env []
  lookup a (Env l) = Prelude.lookup a l

instance (Show a, Pretty b) => Pretty (Env a b) where
  pretty (Env l) = "[" <> separate ", " (map (\(a,b) -> pretty (show a) <> " : " <> pretty b) l) <> " ]"

-- |adjust the value associated with a given key
adjust :: Eq a => (b -> b) -> a -> Env a b -> Env a b
adjust f a (Env [])         = Env []
adjust f a (Env ((k,v):xs)) | a == k    = let v' = f v in Env ((k, f v):xs)
                            | otherwise = let Env ys = adjust f a (Env xs) in Env ((k,v):ys)
