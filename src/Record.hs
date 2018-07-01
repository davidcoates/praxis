module Record
  ( Record
  , fromList
  , toList
  , toCanonicalList
  , pair
  , unpair
  , unit
  , showKeys
  ) where

import           Common

import           Data.List (intercalate)
import           Data.Map  (Map)
import qualified Data.Map  as Map

data Field = Implicit Int
           | Explicit Name
  deriving (Eq, Ord)

newtype Record a = Record { _record :: [(Field, a)] }
  deriving (Eq, Ord)

instance Functor Record where
  fmap f (Record r) = Record (map (\(k, v) -> (k, f v)) r)

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

-- |Conversion to a canonical list representation
toList :: Record a -> [(Maybe Name, a)]
toList (Record r) = map simplify r
  where simplify (Implicit _, a) = (Nothing, a)
        simplify (Explicit n, a) = (Just n, a)

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
