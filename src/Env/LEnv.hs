{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

module Env.LEnv
  ( LEnv

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

import           Common        hiding (value)
import           Env.Env       (Env (..))
import qualified Env.Env       as Env

import           Control.Lens  (makeLenses)
import qualified Data.Map.Lazy as Map
import           Prelude       hiding (lookup, read)
import qualified Prelude       (lookup)


data Entry a = Entry { _value :: a, _used :: Int, _read :: Int }

mkEntry :: a -> Entry a
mkEntry x = Entry { _value = x, _used = 0, _read = 0 }

makeLenses ''Entry

instance Semigroup (Entry a) where
  e1 <> e2 = Entry { _value = view value e1, _used = view used e1 + view used e2, _read = view read e1 + view read e2 }

instance Pretty a => Pretty (Entry a) where
  pretty Entry{ _value, _used, _read } = "[u" <> pretty (show _used) <> ",r" <> pretty (show _read) <> "] " <> pretty _value

-- Linear environment
type LEnv a = Env (Entry a)

empty :: LEnv a
empty = Env.empty

insert :: Name -> a -> LEnv a -> LEnv a
insert k v l = Env.insert k (mkEntry v) l

lookup :: Name -> LEnv a -> Maybe a
lookup k l = view value <$> Env.lookup k l

adjust :: (a -> a) -> Name -> LEnv a -> LEnv a
adjust f k l = Env.adjust (over value f) k l

fromList :: [(Name, a)] -> LEnv a
fromList = \case
  []        -> empty
  ((k,v):l) -> insert k v (fromList l)

incUsed :: Name -> LEnv a -> LEnv a
incUsed k l = Env.adjust (over used (+1)) k l

incRead :: Name -> LEnv a -> LEnv a
incRead k l = Env.adjust (over read (+1)) k l

join :: LEnv a -> LEnv a -> LEnv a
join (Env e1) (Env e2) = Env $ Map.intersectionWith (<>) e1 e2

difference :: LEnv a -> LEnv a -> LEnv a
difference (Env e1) (Env e2) = Env (e1 `Map.difference` e2)

touched :: LEnv a -> LEnv a -> Env a
touched (Env e1) (Env e2) = Env $ Map.map (\(e1, _) -> view value e1) $ Map.filter (\(e1, e2) -> view used e2 > view used e1 || view read e2 > view read e1) $ Map.intersectionWith (,) e1 e2
