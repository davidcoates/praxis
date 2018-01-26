module Check.Env
  ( inc
  , use
  )
where

import Pos
import Type
import AST (Name)
import Check.Derivation
import Check.Error
import Compile

-- |Increment the usage count of a particular variable
inc :: Name -> Env -> Env
inc s                [] = []
inc s (l@(s',(t,i)):ls) = if s == s' then (s',(t,i+1)):ls else l : inc s ls

-- |Increment the usage count of a particular variable, and generate a Share constraint if it has already been used.
use :: Pos -> Name -> Env -> Compiler TypeError (Pure, Env, [Derivation])
use p s l = case lookup s l of Just (t, i) -> let cs = [ newDerivation (shareC t) ("Variable '" ++ s ++ "' used for a second time") p | i /= 0 ]
                                              in pure (t, inc s l, cs)
                               Nothing     -> throwError p (NotInScope s)
