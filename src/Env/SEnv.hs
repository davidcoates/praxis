{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

module Env.SEnv
  ( SEnv(..)

  , lookupTop
  , push
  )
where

import           Common
import           Env
import           Env.Env

import           Control.Arrow (second)
import           Control.Lens  (makeLenses)
import           Data.List     (intercalate)
import           Prelude       hiding (lookup)
import qualified Prelude       (lookup)

-- Scoped Environment
data SEnv a b = SEnv (Env a b) [Env a b]

deriving instance Foldable (SEnv a)
deriving instance Traversable (SEnv a)

instance Functor (SEnv a) where
  fmap f (SEnv l ls) = SEnv (fmap f l) (map (fmap f) ls)

instance (Show a, Pretty b) => Pretty (SEnv a b) where
  pretty (SEnv l ls) = separate "|" (map pretty' (l:ls)) where
    pretty' (Env ls) = "[" <> separate ", " (map (\(a,b) -> pretty (show a) <> " : " <> pretty b) ls) <> "]"

instance Environment SEnv where
  intro a b (SEnv l ls) = SEnv (intro a b l) ls
  elim (SEnv l ls) = SEnv (elim l) ls
  empty = SEnv empty []
  lookup a (SEnv l ls) = f (l:ls) where
    f     [] = Nothing
    f (l:ls) = case Env.lookup a l of
      Just v  -> Just v
      Nothing -> f ls

lookupTop :: Eq a => a -> SEnv a b -> Maybe b
lookupTop a (SEnv l _) = Env.lookup a l

push :: SEnv a b -> SEnv a b
push (SEnv l ls) = SEnv (Env.fromList []) (l:ls)
