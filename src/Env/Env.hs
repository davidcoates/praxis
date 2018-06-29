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

import Data.List (intercalate)
import Prelude hiding (lookup)
import qualified Prelude (lookup)

-- TODO Cosider putting source in Env
newtype Env a b = Env [(a, b)]

fromList :: [(a, b)] -> Env a b
fromList = Env

instance (Show a, Show b) => Show (Env a b) where
  show (Env l) = "[" ++ intercalate ", " (map (\(a,b) -> show a ++ " : " ++ show b) l) ++ " ]"

-- |adjust the value associated with a given key, returns the modified entry if successful
adjust :: Eq a => (b -> b) -> a -> Env a b -> (Maybe (a, b), Env a b)
adjust f a (Env [])         = (Nothing, Env [])
adjust f a (Env ((k,v):xs)) | a == k    = let v' = f v in (Just (k, v'), Env ((k, f v):xs))
                            | otherwise = let (y, Env ys) = adjust f a (Env xs) in (y, Env ((k,v):ys))

elim :: Env a b -> Env a b
elim (Env l) = Env (tail l)

elimN :: Int -> Env a b -> Env a b
elimN n (Env l) = Env (drop n l)

intro :: a -> b -> Env a b -> Env a b
intro a b (Env xs) = Env ((a,b):xs)

lookup :: Eq a => a -> Env a b -> Maybe b
lookup x (Env xs) = Prelude.lookup x xs
