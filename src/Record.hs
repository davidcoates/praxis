module Record
  ( Record
  , fromList
  , toList
  , toCanonicalList
  , pair
  ) where

import Common

import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (intercalate)

data Field = Implicit Int
           | Explicit Name
  deriving (Eq, Ord)

newtype Record a = Record { _record :: [(Field, a)] }
  deriving (Eq, Ord)

instance Functor Record where
  fmap f (Record r) = Record (map (\(k, v) -> (k, f v)) r)

instance Foldable Record where
  foldr f x (Record r) = foldr f x (map snd r)

pair :: a -> a -> Record a
pair x y = fromList [(Nothing, x), (Nothing, y)]

-- TODO what to do on duplicate names? What if names contain the implicit descriptors first second etc?
fromList :: [(Maybe Name, a)] -> Record a
fromList = Record . addDefaults [0..]
  where addDefaults :: [Int] -> [(Maybe Name, a)] -> [(Field, a)]
        addDefaults _ [] = []
        addDefaults is     ((Just n, a):xs)  = (Explicit n, a) : addDefaults is xs
        addDefaults (i:is) ((Nothing, a):xs) = (Implicit i, a) : addDefaults is xs

-- |Conversion to a canonical list representation
toList :: Record a -> [(Maybe Name, a)]
toList (Record r) = map simplify r
  where simplify (Implicit _, a) = (Nothing, a)
        simplify (Explicit n, a) = (Just n, a)

toCanonicalList :: Record a -> [(Maybe Name, a)]
toCanonicalList (Record r) = toList (Record (Map.toList (Map.fromList r)))

instance Show a => Show (Record a) where
  show r = "(" ++ intercalate "," (map showEntry (toList r)) ++ ")" -- TODO
    where showEntry (Nothing, a) = show a
          showEntry (Just n,  a) = n ++ "=" ++ show a

