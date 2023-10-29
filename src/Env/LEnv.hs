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
  , captured

  , empty
  , intro
  , lookup
  , adjust
  , fromList

  , mark
  , capture

  , join
  , mixedUse
  )
where

import           Common       hiding (value)
import           Env.Env      (Env (..))
import qualified Env.Env      as Env

import           Control.Lens (makeLenses)
import           Prelude      hiding (lookup)
import qualified Prelude      (lookup)

data Entry a = Entry { _value :: a, _used :: Bool, _captured :: Bool }

mkEntry :: a -> Entry a
mkEntry x = Entry { _value = x, _used = False, _captured = False }

makeLenses ''Entry

instance Semigroup (Entry a) where
  e1 <> e2 = Entry { _value = view value e1, _used = view used e1 || view used e2, _captured = view captured e1 || view captured e2 }

{-
deriving instance Functor Entry
deriving instance Foldable Entry
deriving instance Traversable Entry
-}

instance Pretty a => Pretty (Entry a) where
  pretty Entry{ _value, _used, _captured } = (<> pretty _value) $ case (_used, _captured) of
    (True, True)   -> "[uc] "
    (True, False)  -> "[u] "
    (False, True)  -> "[c] "
    (False, False) -> ""

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

mark :: Name -> LEnv a -> LEnv a
mark k l = Env.adjust (\v -> v { _used = True} ) k l

capture :: LEnv a -> LEnv a
capture l = fmap (\v -> v { _captured = True}) l

join :: LEnv a -> LEnv a -> LEnv a
join = Env.zipWith (<>)

mixedUse :: LEnv a -> LEnv a -> [(Name, a)]
mixedUse (Env l1) (Env l2) = [ (k, view value e1) | ((k, e1), (_, e2)) <- zip l1 l2, view used e1 /= view used e2 ]
