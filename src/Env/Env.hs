{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StandaloneDeriving #-}

module Env.Env
  ( Env(..)

  , empty
  , intro
  , lookup
  , adjust
  , fromList

  )
where

import           Common
import           Control.Lens (Traversal)
import           Data.List    (intercalate)
import           Prelude      hiding (lookup)
import qualified Prelude      (lookup)

-- TODO Cosider putting source in Env
newtype Env a = Env [(Name, a)]

deriving instance Functor Env
deriving instance Foldable Env
deriving instance Traversable Env

empty :: Env a
empty = Env []

intro :: Name -> a -> Env a -> Env a
intro k v (Env l) = Env ((k, v):l)

lookup :: Name -> Env a -> Maybe a
lookup a (Env l) = Prelude.lookup a l

instance Pretty a => Pretty (Env a) where
  pretty (Env l) = "[" <> separate ", " (map (\(k, v) -> pretty k <> " : " <> pretty v) l) <> " ]"

adjust :: (a -> a) -> Name -> Env a -> Env a
adjust f n (Env ((k, v):l)) | n == k    = Env ((k, f v):l)
                            | otherwise = let Env l' = adjust f n (Env l) in Env ((k, v):l')

fromList :: [(Name, a)] -> Env a
fromList = \case
  []        -> empty
  ((k,v):l) -> intro k v (fromList l)
