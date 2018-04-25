module Check.Env
  ( inc
  , use
  )
where

import Source (Source)
import Type
import AST (Name)
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
