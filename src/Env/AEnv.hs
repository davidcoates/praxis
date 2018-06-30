module Env.AEnv
  ( AEnv
  , fromList

  , elim
  , elimN
  , intro
  , join
  , lookup
  , use
  )
where

import           Env.Env   (Env (..))
import qualified Env.Env   as Env

import           Data.List (intercalate)
import           Prelude   hiding (lookup)
import qualified Prelude   (lookup)

newtype AEnv a b = AEnv (Env a (Bool, b))

fromList :: [(a, b)] -> AEnv a b
fromList = AEnv . Env.fromList . map (\(a, b) -> (a, (False, b)))

instance (Show a, Show b) => Show (AEnv a b) where
  show (AEnv (Env l)) = "[" ++ intercalate ", " (map (\(a,(u,b)) -> show a ++ (if u then " :o " else " :* ") ++ show b) l) ++ " ]"

elim :: AEnv a b -> AEnv a b
elim (AEnv l) = AEnv $ Env.elim l

elimN :: Int -> AEnv a b -> AEnv a b
elimN n (AEnv l) = AEnv $ Env.elimN n l

intro :: a -> b -> AEnv a b -> AEnv a b
intro a b (AEnv l) = AEnv (Env.intro a (False, b) l)

use :: Eq a => a -> AEnv a b -> (Maybe (Bool, b), AEnv a b)
use x (AEnv l) = let (e, l') = Env.adjust (\(_, b) -> (True, b)) x l in (snd <$> e, AEnv l')

lookup :: Eq a => a -> AEnv a b -> Maybe (Bool, b)
lookup x (AEnv l) = Env.lookup x l

join :: (Eq a, Eq b) => AEnv a b -> AEnv a b -> AEnv a b
join (AEnv (Env l1)) (AEnv (Env l2)) = (AEnv . Env) $ join' l1 l2 where
  join' ((x,(xu,xt)):xs) ((y,(yu,yt)):ys) | x == y && xt == yt = (x,(xu || yu,xt)) : join' xs ys
