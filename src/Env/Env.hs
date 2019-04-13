{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE StandaloneDeriving #-}

module Env.Env
  ( Env(..)
  , fromList

  , adjust
  , elim
  , elimN
  , intro
  , lookup
  )
where

import           Common
import           Control.Lens (Traversal)
import           Data.List    (intercalate)
import           Prelude      hiding (lookup)
import qualified Prelude      (lookup)

-- TODO Cosider putting source in Env
newtype Env a b = Env [(a, b)]

deriving instance Foldable (Env a)
deriving instance Traversable (Env a)

instance Functor (Env a) where
  fmap f (Env l) = Env (fmap (over second f) l)

fromList :: [(a, b)] -> Env a b
fromList = Env

instance (Show a, Show b) => Show (Env a b) where
  show (Env l) = "[" ++ intercalate ", " (map (\(a,b) -> show a ++ " : " ++ show b) l) ++ " ]"

-- |adjust the value associated with a given key, returns the modified entry if successful
adjust :: Eq a => (b -> b) -> a -> Env a b -> Env a b
adjust f a (Env [])         = Env []
adjust f a (Env ((k,v):xs)) | a == k    = let v' = f v in Env ((k, f v):xs)
                            | otherwise = let Env ys = adjust f a (Env xs) in Env ((k,v):ys)

elim :: Env a b -> Env a b
elim (Env l) = Env (tail l)

elimN :: Int -> Env a b -> Env a b
elimN n (Env l) = Env (drop n l)

intro :: a -> b -> Env a b -> Env a b
intro a b (Env xs) = Env ((a,b):xs)

lookup :: Eq a => a -> Env a b -> Maybe b
lookup x (Env xs) = Prelude.lookup x xs
