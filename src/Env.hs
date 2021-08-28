module Env
  ( Environment(..)
  , fromList
  )
where

class Environment c where
  intro :: a -> b -> c a b -> c a b
  elim :: c a b -> c a b
  empty :: c a b
  lookup :: Eq a => a -> c a b -> Maybe b

fromList :: Environment c => [(a,b)] -> c a b
fromList = \case
  []        -> empty
  ((a,b):l) -> intro a b (fromList l)
