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

import           Env.Env      (Env (..))
import qualified Env.Env      as Env

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

fromList :: [(a, b)] -> LEnv a b
fromList vs = LEnv (Env.fromList (map (\(a, b) -> (a, (False, b))) vs)) []

instance (Show a, Show b) => Show (LEnv a b) where
  show (LEnv l ls) = intercalate "|" (map show' (l:ls)) where
    show' (Env l) = "[" ++ intercalate ", " (map (\(a,(u,b)) -> show a ++ (if u then " :* " else " :o ") ++ show b) l) ++ " ]"

elim :: LEnv a b -> LEnv a b
elim (LEnv l ls) = LEnv (Env.elim l) ls

elimN :: Int -> LEnv a b -> LEnv a b
elimN n (LEnv l ls) = LEnv (Env.elimN n l) ls

intro :: a -> b -> LEnv a b -> LEnv a b
intro a b (LEnv l ls) = LEnv (Env.intro a (False, b) l) ls

mark :: Eq a => a -> LEnv a b -> LEnv a b
mark x (LEnv l ls) = let (m:ms) = f (l:ls) in LEnv m ms
  where f (l:ls) = case Env.lookup x l of
          Just _  -> Env.adjust (\(_, b) -> (True, b)) x l : ls
          Nothing -> l : f ls

lookup :: Eq a => a -> LEnv a b -> Maybe (Bool, Bool, b)
lookup x (LEnv l ls) = f (l:ls) False
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
