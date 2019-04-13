{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE StandaloneDeriving #-}

module Env.LEnv
  ( LEnv
  , fromList

  , elim
  , elimN
  , intro
  , join
  , lookup
  , mark
  , push
  , pop
  )
where

import           Env.AEnv      (AEnv (..))
import qualified Env.AEnv      as AEnv

import           Control.Arrow (second)
import           Data.List     (intercalate)
import           Prelude       hiding (lookup)
import qualified Prelude       (lookup)

data LEnv a b = LEnv (AEnv a b) [AEnv a b]

deriving instance Foldable (LEnv a)
deriving instance Traversable (LEnv a)

instance Functor (LEnv a) where
  fmap f (LEnv l ls) = LEnv (fmap f l) (map (fmap f) ls)

fromList :: [(a, b)] -> LEnv a b
fromList vs = LEnv (AEnv.fromList vs) []

instance (Show a, Show b) => Show (LEnv a b) where
  show (LEnv l ls) = "[" ++ intercalate "|" (map show (l:ls)) ++ " ]"

elim :: LEnv a b -> LEnv a b
elim (LEnv l ls) = LEnv (AEnv.elim l) ls

elimN :: Int -> LEnv a b -> LEnv a b
elimN n (LEnv l ls) = LEnv (AEnv.elimN n l) ls

intro :: a -> b -> LEnv a b -> LEnv a b
intro a b (LEnv l ls) = LEnv (AEnv.intro a b l) ls

mark :: Eq a => a -> LEnv a b -> LEnv a b
mark x (LEnv l ls) = let (m:ms) = f (l:ls) in LEnv m ms
  where f (l:ls) = case AEnv.lookup x l of
          Just _  -> AEnv.mark x l : ls
          Nothing -> l : f ls

lookup :: Eq a => a -> LEnv a b -> Maybe (Bool, Bool, b)
lookup x (LEnv l ls) = f (l:ls) False
  where f     [] _ = Nothing
        f (l:ls) c = case AEnv.lookup x l of
          Just (u, v) -> Just (c, u, v)
          Nothing     -> f ls True

join :: LEnv a b -> LEnv a b -> LEnv a b
join (LEnv l1 l1s) (LEnv l2 l2s) = LEnv (AEnv.join l1 l2) (zipWith AEnv.join l1s l2s)

push :: LEnv a b -> LEnv a b
push (LEnv l ls) = LEnv (AEnv.fromList []) (l:ls)

pop :: LEnv a b -> LEnv a b
pop (LEnv _ (l:ls)) = LEnv l ls
