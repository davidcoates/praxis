{-# LANGUAGE OverloadedStrings #-}

module Env.Lazy
  ( Env(..)

  , module Map
  , insert
  )
where

import           Common

import           Data.Map.Lazy (Map, adjust, empty, fromList, lookup, toList)
import qualified Data.Map.Lazy as Map
import           Prelude       hiding (lookup)


-- TODO Cosider putting source in Env?
type Env a = Map Name a

insert :: Name -> a -> Env a -> Env a
insert k v e = case Map.lookup k e of
  Nothing -> Map.insert k v e
  Just _  -> error ("double insert: " ++ k)
