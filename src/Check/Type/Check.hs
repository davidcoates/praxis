{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Check.Type.Check
  ( check
  ) where

import           Check.Type.Generate as Generate
import           Check.Type.Require
import           Check.Type.Solve    as Solve
import           Check.Type.System
import           Common
import           Introspect
import           Praxis
import           Stage
import           Term

check :: Term a => Annotated a -> Praxis (Annotated a)
check x = save stage $ do
  stage .= TypeCheck Warmup
  our .= initialSystem
  x <- Generate.run x
  (ts, ops) <- Solve.run
  let f :: forall a. Term a => a -> Maybe a
      f x = case witness :: I a of
        IType -> case x of {   TyUni n ->  lookup n ts; _ -> Nothing }
        ITyOp -> case x of { TyOpUni n -> lookup n ops; _ -> Nothing }
        _     -> Nothing
  x <- normalise (sub f x)
  display x `ifFlag` debug
  return x
  -- TODO type defaulting
