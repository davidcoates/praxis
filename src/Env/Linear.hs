{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

module Env.Linear
  ( Env

  , Entry(..)
  , mkEntry

  , value
  , used
  , read

  , empty
  , insert
  , lookup
  , adjust
  , fromList

  , incUsed
  , incRead

  , join
  , difference
  , touched
  )
where

import           Common          hiding (value)
import qualified Env.Strict      as Strict

import           Control.Lens    (makeLenses)
import qualified Data.Map.Strict as Map
import           Prelude         hiding (lookup, read)
import qualified Prelude         (lookup)


data Entry a = Entry { _value :: a, _used :: Int, _read :: Int }

mkEntry :: a -> Entry a
mkEntry x = Entry { _value = x, _used = 0, _read = 0 }

makeLenses ''Entry

instance Semigroup (Entry a) where
  e1 <> e2 = Entry { _value = view value e1, _used = view used e1 + view used e2, _read = view read e1 + view read e2 }

instance Pretty a => Pretty (Entry a) where
  pretty Entry{ _value, _used, _read } = "[u" <> pretty (show _used) <> ",r" <> pretty (show _read) <> "] " <> pretty _value

type Env a = Strict.Env (Entry a)

empty :: Env a
empty = Strict.empty

insert :: Name -> a -> Env a -> Env a
insert k v l = Strict.insert k (mkEntry v) l

lookup :: Name -> Env a -> Maybe a
lookup k l = view value <$> Strict.lookup k l

adjust :: (a -> a) -> Name -> Env a -> Env a
adjust f k l = Strict.adjust (over value f) k l

fromList :: [(Name, a)] -> Env a
fromList = \case
  []        -> empty
  ((k,v):l) -> insert k v (fromList l)

incUsed :: Name -> Env a -> Env a
incUsed k l = Strict.adjust (over used (+1)) k l

incRead :: Name -> Env a -> Env a
incRead k l = Strict.adjust (over read (+1)) k l

join :: Env a -> Env a -> Env a
join e1 e2 = Map.intersectionWith (<>) e1 e2

difference :: Env a -> Env a -> Env a
difference e1 e2 = e1 `Map.difference` e2

touched :: Env a -> Env a -> Strict.Env a
touched e1 e2 = Map.map (\(e1, _) -> view value e1) $ Map.filter (\(e1, e2) -> view used e2 > view used e1 || view read e2 > view read e1) $ Map.intersectionWith (,) e1 e2
