module Env
  ( Environment(..)
  , elimN
  , fromList
  )
where

class Environment c where
  intro :: a -> b -> c a b -> c a b
  elim :: c a b -> c a b
  empty :: c a b
  lookup :: Eq a => a -> c a b -> Maybe b

elimN :: Environment c => Int -> c a b -> c a b
elimN 0 l = l
elimN n l = elimN (n-1) (elim l)

fromList :: Environment c => [(a,b)] -> c a b
fromList = \case
  []        -> empty
  ((a,b):l) -> intro a b (fromList l)
