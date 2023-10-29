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
  , lookup'
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

makeLenses ''Entry

deriving instance Functor Entry
deriving instance Foldable Entry
deriving instance Traversable Entry

instance Pretty a => Pretty (Entry a) where
  pretty Entry{ _value, _used, _captured } = (<> pretty _value) $ case (_used, _captured) of
    (True, True)   -> "[uc] "
    (True, False)  -> "[u] "
    (False, True)  -> "[c] "
    (False, False) -> ""

-- Linear environment
newtype LEnv a = LEnv (Env (Entry a))

deriving instance Functor LEnv
deriving instance Foldable LEnv
deriving instance Traversable LEnv

instance Pretty a => Pretty (LEnv a) where
  pretty (LEnv l) = pretty l

empty :: LEnv a
empty = LEnv (Env.empty)

intro :: Name -> a -> LEnv a -> LEnv a
intro k v (LEnv l) = LEnv $ Env.intro k (Entry { _value = v, _used = False, _captured = False}) l

lookup :: Name -> LEnv a -> Maybe (Entry a)
lookup k (LEnv l) = Env.lookup k l

lookup' :: Name -> LEnv a -> Maybe a
lookup' k l = view value <$> lookup k l

adjust :: (a -> a) -> Name -> LEnv a -> LEnv a
adjust f k (LEnv l) = LEnv $ Env.adjust (over value f) k l

fromList :: [(Name, a)] -> LEnv a
fromList = \case
  []        -> empty
  ((k,v):l) -> intro k v (fromList l)

mark :: Name -> LEnv a -> LEnv a
mark k (LEnv l) = LEnv (Env.adjust (\v -> v { _used = True} ) k l)

capture :: LEnv a -> LEnv a
capture (LEnv l) = LEnv (fmap (\v -> v { _captured = True}) l)

-- Join is used to unify branches with respect to usage and captured status.
-- E.g. a variable is used/captured by an If expression iff it is used/captured by at least one branch.
join :: LEnv a -> LEnv a -> LEnv a
join (LEnv l1) (LEnv l2) = LEnv (join' l1 l2) where
  join' (Env l1) (Env l2) = Env $ zipWith (\(k, v1) (_, v2) -> (k, Entry { _value = view value v1, _used = view used v1 || view used v2, _captured = view captured v1 || view captured v2 })) l1 l2

mixedUse :: LEnv a -> LEnv a -> [(Name, a)]
mixedUse (LEnv l1) (LEnv l2) = mixedUse' l1 l2 where
  mixedUse' (Env l1) (Env l2) = [ (k, view value v1) | ((k, v1), (_, v2)) <- zip l1 l2, view used v1 /= view used v2 ]
