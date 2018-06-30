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

import           Compiler
import           Env              (TEnv)
import           Env.AEnv         (AEnv, fromList)
import qualified Env.AEnv         as AEnv

import           Check.Derivation
import           Common
import           Error
import           Source           (Source)
import           Type

import           Prelude          hiding (read)


elim :: Compiler ()
elim = do
  l <- get tEnv
  set tEnv (AEnv.elim l)

elimN :: Int -> Compiler ()
elimN n = do
  l <- get tEnv
  set tEnv (AEnv.elimN n l)

intro :: Name -> Pure -> Compiler ()
intro n p = over tEnv (AEnv.intro n p)

join :: Compiler a -> Compiler b -> Compiler (a, b)
join f1 f2 = do
  l <- get tEnv
  x <- f1
  l1 <- get tEnv
  set tEnv l
  y <- f2
  l2 <- get tEnv
  set tEnv (AEnv.join l1 l2)
  return (x, y)

read :: Source -> Name -> Compiler (Pure, [Derivation])
read s n = do
  l <- get tEnv
  case AEnv.lookup n l of
    Just (u, t) -> do
      let c1 = [ newDerivation (share t) ("Variable '" ++ n ++ "' used before let bang") s | not u ]
      b <- get inClosure
      let c2 = [ newDerivation (share t) ("Variable '" ++ n ++ "' captured") s | b ]
      return (t, c1 ++ c2)
    Nothing     -> throwError (CheckError (NotInScope n s))

-- |Marks a variable as used, and generate a Share constraint if it has already been used.
use :: Source -> Name -> Compiler (Pure, [Derivation])
use s n = do
  l <- get tEnv
  let (e, l') = AEnv.use n l
  case e of
    Just (u, t) -> do
      let c1 = [ newDerivation (share t) ("Variable '" ++ n ++ "' used for a second time") s | u ]
      b <- get inClosure
      let c2 = [ newDerivation (share t) ("Variable '" ++ n ++ "' captured") s | b ]
      return (t, c1 ++ c2)
    Nothing     -> throwError (CheckError (NotInScope n s))
