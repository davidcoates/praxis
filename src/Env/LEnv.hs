{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

module Env.LEnv
  ( LEnv

  , Entry
  , value
  , used
  , captured

  , lookupFull
  , adjust

  , mark
  , capture
  , join
  )
where

import           Common        hiding (value)
import           Env
import           Env.Env (Env(..))
import qualified Env.Env as Env

import           Control.Arrow (second)
import           Control.Lens  (makeLenses)
import           Data.List     (intercalate)
import           Prelude       hiding (lookup)
import qualified Prelude       (lookup)

data Entry b = Entry { _value :: b, _used :: Bool, _captured :: Bool }

deriving instance Functor Entry
deriving instance Foldable Entry
deriving instance Traversable Entry

makeLenses ''Entry

instance Pretty b => Pretty (Entry b) where
  pretty b = (<> pretty (view value b)) $ case (view used b, view captured b) of
    (True, True)   -> "[uc] "
    (True, False)  -> "[u] "
    (False, True)  -> "[c] "
    (False, False) -> ""

-- Linear environment
newtype LEnv a b = LEnv (Env a (Entry b))

deriving instance Foldable (LEnv a)
deriving instance Traversable (LEnv a)

instance Functor (LEnv a) where
  fmap f (LEnv l) = LEnv (fmap (over value f) l)

instance (Show a, Pretty b) => Pretty (LEnv a b) where
  pretty (LEnv l) = pretty l

instance Environment LEnv where
  intro a b (LEnv l) = LEnv (intro a b' l) where
    b' = Entry { _value = b, _used = False, _captured = False }
  elim (LEnv l) = LEnv (elim l)
  empty = LEnv empty
  lookup a (LEnv l) = fmap (view value) (lookup a l)

lookupFull :: Eq a => a -> LEnv a b -> Maybe (Entry b)
lookupFull a (LEnv l) = lookup a l

mark :: Eq a => a -> LEnv a b -> LEnv a b
mark a (LEnv l) = LEnv (Env.adjust (\b -> b { _used = True} ) a l)

capture :: LEnv a b -> LEnv a b
capture (LEnv l) = LEnv (fmap (\b -> b { _captured = True}) l)

adjust :: Eq a => (b -> b) -> a -> LEnv a b -> LEnv a b
adjust f a (LEnv l) = LEnv (Env.adjust (over value f) a l)

-- Join is used to unify branches with respect to usage and captured status.
-- E.g. a variable is used/captured by an If expression iff it is used/captured by at least one branch.
join :: LEnv a b -> LEnv a b -> LEnv a b
join (LEnv l1) (LEnv l2) = LEnv (join' l1 l2) where
  join' (Env l1) (Env l2) = Env (zipWith (\(x, xb) (_, yb) -> (x, Entry { _value = view value xb, _used = view used xb || view used yb, _captured = view captured xb || view captured yb })) l1 l2)
