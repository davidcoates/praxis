module Record
  ( Record
  , fromList
  , toList
  , toCanonicalList
  , keys
  , pair
  , unpair
  , unit
  , showKeys
  ) where

import           Common

import           Control.Arrow (second)
import           Data.List     (intercalate)
import           Data.Map      (Map)
import qualified Data.Map      as Map

data Field = Implicit Int
           | Explicit Name
  deriving (Eq, Ord)

newtype Record a = Record { _record :: [(Field, a)] }

instance Eq a => Eq (Record a) where
  r == s = toCanonicalList r == toCanonicalList s

instance Ord a => Ord (Record a) where
  r `compare` s = toCanonicalList r `compare` toCanonicalList s

instance Functor Record where
  fmap f (Record r) = Record (map (second f) r)

instance Foldable Record where
  foldr f x (Record r) = foldr f x (map snd r)

instance Traversable Record where
  traverse f (Record r) = Record <$> traverse (\(k,v) -> (\v -> (k,v)) <$> f v) r

unit :: Record a
unit = Record []

pair :: a -> a -> Record a
pair x y = fromList [(Nothing, x), (Nothing, y)]

unpair :: Record a -> (a, a)
unpair (Record [(Implicit 0, x), (Implicit 1, y)]) = (x, y)
-- TODO do a nice lookup function

-- TODO what to do on duplicate names? What if names contain the implicit descriptors _1 _2 etc?
fromList :: [(Maybe Name, a)] -> Record a
fromList = Record . addDefaults [0..]
  where addDefaults :: [Int] -> [(Maybe Name, a)] -> [(Field, a)]
        addDefaults _      []                = []
        addDefaults is     ((Just n, a):xs)  = (Explicit n, a) : addDefaults is xs
        addDefaults (i:is) ((Nothing, a):xs) = (Implicit i, a) : addDefaults is xs

toList :: Record a -> [(Maybe Name, a)]
toList (Record r) = map simplify r
  where simplify (Implicit _, a) = (Nothing, a)
        simplify (Explicit n, a) = (Just n, a)

keys :: Record a -> [Field]
keys (Record r) = map fst r

-- |Conversion to a canonical list representation
toCanonicalList :: Record a -> [(Maybe Name, a)]
toCanonicalList (Record r) = toList (Record (Map.toList (Map.fromList r)))

instance Show a => Show (Record a) where
  show r = "(" ++ intercalate ", " (map showEntry (toList r)) ++ ")" -- TODO
    where showEntry (Nothing, a) = show a
          showEntry (Just n,  a) = n ++ "=" ++ show a

showKeys :: Record a -> String
showKeys r = "(" ++ intercalate ", " (map showKey (toList r)) ++ ")"
  where showKey (Nothing, _) = "_"
        showKey (Just n,  _) = n ++ "=_"
