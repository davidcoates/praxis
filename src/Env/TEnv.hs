module Env.TEnv
  ( TEnv
  , fromList

  , elim
  , elimN
  , intro
  , join
  , lookup
  , read
  , use
  , closure
  )
where

import           Check.Constraint
import           Check.System
import           Common
import           Env              (TEnv)
import           Env.LEnv         (LEnv, fromList)
import qualified Env.LEnv         as LEnv
import           Error
import           Praxis
import           Source           (Source)
import           Tag
import           Type

import           Control.Monad    (replicateM)
import           Prelude          hiding (log, lookup, read)
import qualified Prelude          (lookup)


elim :: Praxis ()
elim = over tEnv LEnv.elim

elimN :: Int -> Praxis ()
elimN n = over tEnv (LEnv.elimN n)

intro :: Name -> Kinded QType -> Praxis ()
intro n p = over tEnv (LEnv.intro n p)

join :: Praxis a -> Praxis b -> Praxis (a, b)
join f1 f2 = do
  l <- get tEnv
  x <- f1
  l1 <- get tEnv
  set tEnv l
  y <- f2
  l2 <- get tEnv
  set tEnv (LEnv.join l1 l2)
  return (x, y)

closure :: Praxis a -> Praxis a
closure x = do
  over tEnv LEnv.push
  r <- x
  over tEnv LEnv.pop
  return r

-- TODO reduce duplicaiton here
read :: Source -> Name -> Praxis (Kinded Type)
read s n = do
  l <- get tEnv
  case LEnv.lookup n l of
    Just (c, u, t) -> do
      t <- ungeneralise t
      requireAll [ newDerivation (share t) (UnsafeView n) s | not u ]
      requireAll [ newDerivation (share t) (Captured n) s   | c ]
      return t
    Nothing     -> throwError (CheckError (NotInScope n s))

-- |Marks a variable as used, and generate a Share constraint if it has already been used.
use :: Source -> Name -> Praxis (Kinded Type)
use s n = do
  l <- get tEnv
  case LEnv.lookup n l of
    Just (c, u, t) -> do
      set tEnv (LEnv.use n l)
      t <- ungeneralise t
      requireAll [ newDerivation (share t) (Shared n)   s | u ]
      requireAll [ newDerivation (share t) (Captured n) s | c ]
      return t
    Nothing     -> throwError (CheckError (NotInScope n s))

lookup :: Name -> Praxis (Maybe (Kinded QType))
lookup n = do
  l <- get tEnv
  case LEnv.lookup n l of
    Just (_, _, t) -> return (Just t)
    Nothing        -> return Nothing

{-
TODO, want to allow things like:
f : forall a. a -> a
f x = x : a -- This a refers to the a introduced by f

Which means we need some map from TyVars to TyUnis
So that in-scope TyVars can get subbed.

Alternative is to transform the source which would mess up error messages

OR don't allow this, and don't allow explicit forall.
-}
ungeneralise :: Kinded QType -> Praxis (Kinded Type)
ungeneralise (k :< Mono t) = return (k :< t)
ungeneralise x@(KindType :< Forall vs cs (KindType :< t)) = do
  sub <- zipWith (\(n, k) (_ :< t) -> (n, k :< t)) vs <$> replicateM (length vs) freshUniT
  let f :: TypeTraversable a => a -> a
      f = tySub (`Prelude.lookup` sub)
  let cs' = [] -- FIXME TODO derivations derived from cs
  let t' = f (KindType :< t)
  log Debug t'
  over (system . axioms) (++ cs')
  return t'


