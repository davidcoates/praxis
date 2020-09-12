{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StandaloneDeriving #-}

module Env.LEnv
  ( LEnv

  , join
  , lookupFull
  , mark
  , push
  , pop
  )
where

import           Common
import           Env
import           Env.Env

import           Control.Arrow (second)
import           Data.List     (intercalate)
import           Prelude       hiding (lookup)
import qualified Prelude       (lookup)

data LEnv a b = LEnv (Env a (Bool, b)) [Env a (Bool, b)]

deriving instance Foldable (LEnv a)
deriving instance Traversable (LEnv a)

instance Functor (LEnv a) where
  fmap f (LEnv l ls) = LEnv (fmap f' l) (map (fmap f') ls) where
    f' (u, x) = (u, f x)

instance (Show a, Pretty b) => Pretty (LEnv a b) where
  pretty (LEnv l ls) = separate "|" (map pretty' (l:ls)) where
    pretty' (Env l) = "[" <> separate ", " (map (\(a,(u,b)) -> pretty (show a) <> (if u then " :* " else " :o ") <> pretty b) l) <> " ]"

instance Environment LEnv where
  intro a b (LEnv l ls) = LEnv (intro a (False, b) l) ls
  elim (LEnv l ls) = LEnv (elim l) ls
  empty = LEnv empty []
  lookup a l = case lookupFull a l of
    Nothing        -> Nothing
    Just (_, _, b) -> Just b

mark :: Eq a => a -> LEnv a b -> LEnv a b
mark x (LEnv l ls) = let (m:ms) = f (l:ls) in LEnv m ms
  where f (l:ls) = case Env.lookup x l of
          Just _  -> adjust (\(_, b) -> (True, b)) x l : ls
          Nothing -> l : f ls

lookupFull :: Eq a => a -> LEnv a b -> Maybe (Bool, Bool, b)
lookupFull x (LEnv l ls) = f (l:ls) False
  where f     [] _ = Nothing
        f (l:ls) c = case Env.lookup x l of
          Just (u, v) -> Just (c, u, v)
          Nothing     -> f ls True

join :: LEnv a b -> LEnv a b -> LEnv a b
join (LEnv l1 l1s) (LEnv l2 l2s) = LEnv (join' l1 l2) (zipWith join' l1s l2s) where
  join' (Env l1) (Env l2) = Env (zipWith (\(x,(xu,xt)) (y,(yu,yt)) -> (x,(xu || yu, xt))) l1 l2)

push :: LEnv a b -> LEnv a b
push (LEnv l ls) = LEnv (Env.fromList []) (l:ls)

pop :: LEnv a b -> LEnv a b
pop (LEnv _ (l:ls)) = LEnv l ls
