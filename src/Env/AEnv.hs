{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE StandaloneDeriving #-}

module Env.AEnv
  ( AEnv
  , fromList

  , elim
  , elimN
  , intro
  , join
  , lookup
  , mark
  )
where

import           Env.Env       (Env (..))
import qualified Env.Env       as Env

import           Control.Arrow (second)
import           Data.List     (intercalate)
import           Prelude       hiding (lookup)
import qualified Prelude       (lookup)

newtype AEnv a b = AEnv (Env a (Bool, b))

deriving instance Foldable (AEnv a)
deriving instance Traversable (AEnv a)

instance Functor (AEnv a) where
  fmap f (AEnv l) = AEnv (fmap (second f) l)

fromList :: [(a, b)] -> AEnv a b
fromList = AEnv . Env.fromList . map (\(a, b) -> (a, (False, b)))

instance (Show a, Show b) => Show (AEnv a b) where
  show (AEnv (Env l)) = "[" ++ intercalate ", " (map (\(a,(u,b)) -> show a ++ (if u then " :* " else " :o ") ++ show b) l) ++ " ]"

elim :: AEnv a b -> AEnv a b
elim (AEnv l) = AEnv $ Env.elim l

elimN :: Int -> AEnv a b -> AEnv a b
elimN n (AEnv l) = AEnv $ Env.elimN n l

intro :: a -> b -> AEnv a b -> AEnv a b
intro a b (AEnv l) = AEnv (Env.intro a (False, b) l)

mark :: Eq a => a -> AEnv a b -> AEnv a b
mark x (AEnv l) = AEnv $ Env.adjust (\(_, b) -> (True, b)) x l

lookup :: Eq a => a -> AEnv a b -> Maybe (Bool, b)
lookup x (AEnv l) = Env.lookup x l

join :: AEnv a b -> AEnv a b -> AEnv a b
join (AEnv (Env l1)) (AEnv (Env l2)) = (AEnv . Env) $ join' l1 l2 where
  join' ((x,(xu,xt)):xs) ((y,(yu,yt)):ys) = (x, (xu || yu, xt)) : join' xs ys
  join'               []               [] = []
