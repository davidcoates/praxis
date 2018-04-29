module Record
  ( Record
  , fromList
  , toList
  ) where

import Common

import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (intercalate)

data Field = Implicit Int
           | Explicit Name
  deriving (Eq, Ord) -- Note: Derived Ord ensures Implicit < Explicit

newtype Record a = Record { _record :: Map Field a }
  deriving (Eq)

-- TODO what to do on duplicate names? What if names contain the implicit descriptors first second etc?
fromList :: [(Maybe Name, a)] -> Record a
fromList = Record . Map.fromList . addDefaults [0..]
  where addDefaults :: [Int] -> [(Maybe Name, a)] -> [(Field, a)]
        addDefaults _ [] = []
        addDefaults is     ((Just n, a):xs)  = (Explicit n, a) : addDefaults is xs
        addDefaults (i:is) ((Nothing, a):xs) = (Implicit i, a) : addDefaults is xs

-- |Conversion to a canonical list representation
toList :: Record a -> [(Maybe Name, a)]
toList (Record m) = map simplify (Map.toList m)
  where simplify (Implicit _, a) = (Nothing, a)
        simplify (Explicit n, a) = (Just n, a)

instance Show a => Show (Record a) where
  show r = "(" ++ intercalate "," (map showEntry (toList r)) ++ ")" -- TODO
    where showEntry (Nothing, a) = show a
          showEntry (Just n,  a) = n ++ "=" ++ show a

