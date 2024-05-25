{-# LANGUAGE OverloadedStrings #-}

module Env.Strict
  ( Env(..)

  , module Map
  , insert
  )
where

import           Common

import           Data.Map.Strict (Map, adjust, empty, fromList, lookup, toList)
import qualified Data.Map.Strict as Map
import           Prelude         hiding (lookup)


-- TODO Cosider putting source in Env?
type Env a = Map Name a

insert :: Name -> a -> Env a -> Env a
insert k v e = case Map.lookup k e of
  Nothing -> Map.insert k v e
  Just _  -> error ("double insert: " ++ k)

instance (Pretty k, Pretty v) => Pretty (Map k v) where
  pretty m = "[" <> separate ", " (map (\(k, v) -> pretty k <> " : " <> pretty v) (Map.toList m)) <> " ]"
