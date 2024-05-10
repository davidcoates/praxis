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

  , empty
  , intro
  , lookup
  , adjust
  , fromList

  , incUsed
  , incRead

  , join
  )
where

import           Common       hiding (value)
import           Env.Env      (Env (..))
import qualified Env.Env      as Env

import           Control.Lens (makeLenses)
import           Prelude      hiding (lookup, read)
import qualified Prelude      (lookup)

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

incUsed :: Name -> LEnv a -> LEnv a
incUsed k l = Env.adjust (over used (+1)) k l

incRead :: Name -> LEnv a -> LEnv a
incRead k l = Env.adjust (over read (+1)) k l

join :: LEnv a -> LEnv a -> LEnv a
join = Env.zipWith (<>)
