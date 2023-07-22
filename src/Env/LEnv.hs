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
  , lookupTop
  , push

  , mark
  , capture
  , join
  )
where

import           Common        hiding (value)
import           Env
import           Env.Env
import           Env.SEnv      (SEnv (..))
import qualified Env.SEnv      as SEnv

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
data LEnv a b = LEnv (SEnv a (Entry b))

deriving instance Foldable (LEnv a)
deriving instance Traversable (LEnv a)

instance Functor (LEnv a) where
  fmap f (LEnv s) = LEnv (fmap (over value f) s)

instance (Show a, Pretty b) => Pretty (LEnv a b) where
  pretty (LEnv s) = pretty s

instance Environment LEnv where
  intro a b (LEnv s) = LEnv (intro a b' s) where
    b' = Entry { _value = b, _used = False, _captured = False }
  elim (LEnv s) = LEnv (elim s)
  empty = LEnv empty
  lookup a (LEnv s) = fmap (view value) (lookup a s)


lookupFull :: Eq a => a -> LEnv a b -> Maybe (Entry b)
lookupFull a (LEnv s) = lookup a s

lookupTop :: Eq a => a -> LEnv a b -> Maybe (Entry b)
lookupTop a (LEnv s) = SEnv.lookupTop a s

push :: LEnv a b -> LEnv a b
push (LEnv s) = LEnv (SEnv.push s)

mark :: Eq a => a -> LEnv a b -> LEnv a b
mark x (LEnv (SEnv l ls)) = let (m:ms) = f (l:ls) in LEnv (SEnv m ms)
  where f (l:ls) = case lookup x l of
          Just _  -> adjust (\b -> b { _used = True} ) x l : ls
          Nothing -> l : f ls

capture :: LEnv a b -> LEnv a b
capture (LEnv s) = LEnv (fmap (\b -> b { _captured = True}) s)

-- Join is used to unify branches with respect to usage and captured status.
-- E.g. a variable is used/captured by an If expression iff it is used/captured by at least one branch.
join :: LEnv a b -> LEnv a b -> LEnv a b
join (LEnv (SEnv l1 l1s)) (LEnv (SEnv l2 l2s)) = LEnv (SEnv (join' l1 l2) (zipWith join' l1s l2s)) where
  join' (Env l1) (Env l2) = Env (zipWith (\(x, xb) (_, yb) -> (x, Entry { _value = view value xb, _used = view used xb || view used yb, _captured = view captured xb || view captured yb })) l1 l2)
