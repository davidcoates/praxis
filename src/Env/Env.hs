{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StandaloneDeriving #-}

module Env.Env
  ( Env(..)

  , empty
  , insert
  , lookup
  , adjust
  , fromList
  , toList
  )
where

import           Common

import           Control.Lens  (Traversal)
import           Data.List     (intercalate)
import           Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map
import           Prelude       hiding (lookup)


-- TODO Cosider putting source in Env?
newtype Env a = Env (Map Name a)

deriving instance Functor Env
deriving instance Foldable Env
deriving instance Traversable Env

empty :: Env a
empty = Env Map.empty

insert :: Name -> a -> Env a -> Env a
insert k v (Env e) = case Map.lookup k e of
  Nothing -> Env (Map.insert k v e)
  Just _  -> error ("double insert: " ++ k)

lookup :: Name -> Env a -> Maybe a
lookup k (Env e) = Map.lookup k e

adjust :: (a -> a) -> Name -> Env a -> Env a
adjust f k (Env e) = Env (Map.adjust f k e)

fromList :: [(Name, a)] -> Env a
fromList = Env . Map.fromList

toList :: Env a -> [(Name, a)]
toList (Env e) = Map.toList e

instance Pretty a => Pretty (Env a) where
  pretty (Env e) = "[" <> separate ", " (map (\(k, v) -> pretty k <> " : " <> pretty v) (Map.toList e)) <> " ]"
