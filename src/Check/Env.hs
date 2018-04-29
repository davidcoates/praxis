module Check.Env
  ( inc
  , use
  , readUse
  , intro
  , elim
  )
where

import Source (Source)
import Type
import Common
import Check.Derivation
import Compiler
import Error

-- |Increment the usage count of a particular variable
inc :: Name -> Env -> Env
inc s                [] = []
inc s (l@(s',(t,i)):ls) = if s == s' then (s',(t,i+1)):ls else l : inc s ls

-- |Increment the usage count of a particular variable, and generate a Share constraint if it has already been used.
use :: Source -> Name -> Env -> Compiler (Pure, Env, [Derivation])
use s n l = case lookup n l of
  Just (t, i) -> let cs = [ newDerivation (shareC t) ("Variable '" ++ n ++ "' used for a second time") s | i /= 0 ]
                  in pure (t, inc n l, cs)
  Nothing     -> throwError (CheckError (NotInScope n))

readUse :: Source -> Name -> Env -> Compiler (Pure, [Derivation])
readUse s n l = case lookup n l of
  Just (t, i) -> let cs = [ newDerivation (shareC t) ("Variable '" ++ n ++ "' used before let bang") s | i == 0 ]
                  in pure (t, cs)
  Nothing     -> throwError (CheckError (NotInScope n))

intro :: (Name, Pure) -> Env -> Env
intro (n, p) l = (n, (p, 0)) : l

elim :: Source -> Env -> (Env, [Derivation])
elim s ((n, (p, i)) : l) = (l, [ newDerivation (dropC p) ("Variable '" ++ n ++ "' not used") s | i == 0 ])
