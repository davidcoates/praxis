module Env.TEnv
  ( TEnv
  , fromList

  , elim
  , elimN
  , intro
  , join
  , lookup
  , read
  , mark
  , closure

  , ungeneralise
  )
where

import           Annotate
import           Check.Error
import           Check.System
import           Check.Type.Reason
import           Check.Type.Require
import           Check.Type.System
import           Common
import           Env                (TEnv)
import           Env.LEnv           (LEnv, fromList)
import qualified Env.LEnv           as LEnv
import           Introspect         (sub)
import           Praxis
import           Type

import           Control.Monad      (replicateM)
import           Prelude            hiding (log, lookup, read)
import qualified Prelude            (lookup)


elim :: Praxis ()
elim = tEnv %= LEnv.elim

elimN :: Int -> Praxis ()
elimN n = tEnv %= LEnv.elimN n

intro :: Name -> Typed QType -> Praxis ()
intro n p = tEnv %= LEnv.intro n p

join :: Praxis a -> Praxis b -> Praxis (a, b)
join f1 f2 = do
  l <- use tEnv
  x <- f1
  l1 <- use tEnv
  tEnv .= l
  y <- f2
  l2 <- use tEnv
  tEnv .= LEnv.join l1 l2
  return (x, y)

closure :: Praxis a -> Praxis a
closure x = do
  tEnv %= LEnv.push
  r <- x
  tEnv %= LEnv.pop
  return r

-- TODO reduce duplication here
read :: Source -> Name -> Praxis (Typed Type)
read s n = do
  l <- use tEnv
  case LEnv.lookup n l of
    Just (c, u, t) -> do
      t <- ungeneralise s t
      requires [ newConstraint (share t) (UnsafeView n) s | not u ]
      requires [ newConstraint (share t) (Captured n) s   | c ]
      return t
    Nothing     -> throwAt s (NotInScope n)

-- |Marks a variable as used, and generate a Share constraint if it has already been used.
mark :: Source -> Name -> Praxis (Typed Type)
mark s n = do
  l <- use tEnv
  case LEnv.lookup n l of
    Just (c, u, t) -> do
      tEnv .= LEnv.mark n l
      t <- ungeneralise s t
      requires [ newConstraint (share t) (Shared n)   s | u ]
      requires [ newConstraint (share t) (Captured n) s | c ]
      return t
    Nothing     -> throwAt s (NotInScope n)

lookup :: Name -> Praxis (Maybe (Typed QType))
lookup n = do
  l <- use tEnv
  case LEnv.lookup n l of
    Just (_, _, t) -> return (Just t)
    Nothing        -> return Nothing

{-
TODO, want to allow things like:
f : forall a. a -> a
f x = x : a -- This a refers to the a introduced by f

Which means we need some map from TyVars to TyUnis
So that in-scope TyVars can use subbed.

Alternative is to transform the source which would mess up error messages

OR don't allow this, and don't allow explicit forall.
-}
-- TODO move this somewhere else
ungeneralise :: Source -> Typed QType -> Praxis (Typed Type)
ungeneralise _ (_ :< Mono t) = return t
ungeneralise _ (_ :< Forall vs t) = do
  -- TODO need to stores kinds somewhere?
  l <- zipWith (\n (_ :< t) -> (n, t)) vs <$> replicateM (length vs) freshUniT
  return $ sub (\t -> case t of { TyVar n -> n `Prelude.lookup` l; _ -> Nothing }) t
