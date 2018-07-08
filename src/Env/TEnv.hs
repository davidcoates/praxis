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
  )
where

import           Check.Constraint
import           Common
import           Env              (TEnv)
import           Env.AEnv         (AEnv, fromList)
import qualified Env.AEnv         as AEnv
import           Error
import           Praxis
import           Source           (Source)
import           Tag
import           Type

import           Prelude          hiding (log, lookup, read)
import qualified Prelude          (lookup)


elim :: Praxis ()
elim = do
  l <- get tEnv
  set tEnv (AEnv.elim l)

elimN :: Int -> Praxis ()
elimN n = do
  l <- get tEnv
  set tEnv (AEnv.elimN n l)

intro :: Name -> Kinded QType -> Praxis ()
intro n p = over tEnv (AEnv.intro n p)

join :: Praxis a -> Praxis b -> Praxis (a, b)
join f1 f2 = do
  l <- get tEnv
  x <- f1
  l1 <- get tEnv
  set tEnv l
  y <- f2
  l2 <- get tEnv
  set tEnv (AEnv.join l1 l2)
  return (x, y)

-- TODO reduce duplicaiton here

read :: Source -> Name -> Praxis (Kinded Type, [Derivation])
read s n = do
  l <- get tEnv
  case AEnv.lookup n l of
    Just (u, t) -> do
      t <- ungeneralise t
      let c1 = [ newDerivation (share t) (UnsafeView n) s | not u ]
      b <- get inClosure
      let c2 = [ newDerivation (share t) (Captured n) s | b ]
      return (t, c1 ++ c2)
    Nothing     -> throwError (CheckError (NotInScope n s))

-- |Marks a variable as used, and generate a Share constraint if it has already been used.
use :: Source -> Name -> Praxis (Kinded Type, [Derivation])
use s n = do
  l <- get tEnv
  let (e, l') = AEnv.use n l
  case e of
    Just (u, t) -> do
      t <- ungeneralise t
      let c1 = [ newDerivation (share t) (Shared n) s | u ]
      b <- get inClosure
      let c2 = [ newDerivation (share t) (Captured n) s | b ]
      return (t, c1 ++ c2)
    Nothing     -> throwError (CheckError (NotInScope n s))

lookup :: Name -> Praxis (Maybe (Kinded QType))
lookup n = do
  l <- get tEnv
  case AEnv.lookup n l of
    Just (_, t) -> return (Just t)
    Nothing     -> return Nothing

ungeneralise :: Kinded QType -> Praxis (Kinded Type)
ungeneralise (k :< Mono t) = return (k :< t)
ungeneralise t             = error ("ungeneralise: " ++ show t)
