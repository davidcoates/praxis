module Env.TEnv
  ( TEnv
  , fromList

  , elim
  , elimN
  , intro
  , join
  , read
  , use
  )
where

import           Env              (TEnv)
import           Env.AEnv         (AEnv, fromList)
import qualified Env.AEnv         as AEnv
import           Praxis

import           Check.Derivation
import           Common
import           Error
import           Source           (Source)
import           Type

import           Prelude          hiding (read)


elim :: Praxis ()
elim = do
  l <- get tEnv
  set tEnv (AEnv.elim l)

elimN :: Int -> Praxis ()
elimN n = do
  l <- get tEnv
  set tEnv (AEnv.elimN n l)

intro :: Name -> Type -> Praxis ()
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

read :: Source -> Name -> Praxis (Pure, [Derivation])
read s n = do
  l <- get tEnv
  case AEnv.lookup n l of
    Just (u, t) -> do
      (t, c3) <- ungeneralise t
      let c1 = [ newDerivation (share t) ("Variable '" ++ n ++ "' used before let bang") s | not u ]
      b <- get inClosure
      let c2 = [ newDerivation (share t) ("Variable '" ++ n ++ "' captured") s | b ]
      let c4 = map (\c -> newDerivation c ("Variable '" ++ n ++ "' expanded") s) c3
      return (t, c1 ++ c2 ++ c4)
    Nothing     -> throwError (CheckError (NotInScope n s))

-- |Marks a variable as used, and generate a Share constraint if it has already been used.
use :: Source -> Name -> Praxis (Pure, [Derivation])
use s n = do
  l <- get tEnv
  let (e, l') = AEnv.use n l
  case e of
    Just (u, t) -> do
      (t, c3) <- ungeneralise t
      let c1 = [ newDerivation (share t) ("Variable '" ++ n ++ "' used for a second time") s | u ]
      b <- get inClosure
      let c2 = [ newDerivation (share t) ("Variable '" ++ n ++ "' captured") s | b ]
      let c4 = map (\c -> newDerivation c ("Variable '" ++ n ++ "' expanded") s) c3
      return (t, c1 ++ c2 ++ c4)
    Nothing     -> throwError (CheckError (NotInScope n s))


-- TODO: Allow quantified effects
ungeneralise :: Type -> Praxis (Pure, [Constraint])
ungeneralise (Mono (t :# _)) = return (t, [])
ungeneralise (Forall cs as t) = do
  bs <- sequence (replicate (length as) freshUniP)
  let ft = (`lookup` zip as bs)
  let fe = const Nothing
  let subsP = subsPure ft fe
  return (subsP t, map (\c -> case c of Class s t -> Class s (subsP t)) cs)
