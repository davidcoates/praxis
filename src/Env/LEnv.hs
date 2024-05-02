{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

module Env.LEnv
  ( LEnv

  , value
  , used
  , read
  , touched

  , empty
  , intro
  , lookup
  , adjust
  , fromList

  , setUsed
  , setRead

  , join
  )
where

import           Common       hiding (value)
import           Env.Env      (Env (..))
import qualified Env.Env      as Env

import           Control.Lens (makeLenses)
import           Prelude      hiding (lookup, read)
import qualified Prelude      (lookup)

data Entry a = Entry { _value :: a, _used :: Bool, _read :: Bool }

mkEntry :: a -> Entry a
mkEntry x = Entry { _value = x, _used = False, _read = False }

makeLenses ''Entry

instance Semigroup (Entry a) where
  e1 <> e2 = Entry { _value = view value e1, _used = view used e1 || view used e2, _read = view read e1 || view read e2 }

instance Pretty a => Pretty (Entry a) where
  pretty Entry{ _value, _used, _read } = (<> pretty _value) $ ((if _used then "(u)" else "") <> (if _read then "(r)" else ""))

touched :: Entry a -> Bool
touched Entry{ _used, _read } = _used || _read

-- Linear environment
type LEnv a = Env (Entry a)

empty :: LEnv a
empty = Env.empty

intro :: Name -> a -> LEnv a -> LEnv a
intro k v l = Env.intro k (mkEntry v) l

lookup :: Name -> LEnv a -> Maybe a
lookup k l = view value <$> Env.lookup k l

adjust :: (a -> a) -> Name -> LEnv a -> LEnv a
adjust f k l = Env.adjust (over value f) k l

fromList :: [(Name, a)] -> LEnv a
fromList = \case
  []        -> empty
  ((k,v):l) -> intro k v (fromList l)

setUsed :: Name -> LEnv a -> LEnv a
setUsed k l = Env.adjust (\v -> v { _used = True } ) k l

setRead :: Name -> LEnv a -> LEnv a
setRead k l = Env.adjust (\v -> v { _read = True } ) k l

join :: LEnv a -> LEnv a -> LEnv a
join = Env.zipWith (<>)
