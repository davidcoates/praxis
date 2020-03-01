module Check.Type.Check
  ( check
  ) where

import           Check.Type.Generate
import           Check.Type.Require
import           Check.Type.Solve
import           Check.Type.System
import           Common
import           Introspect
import           Praxis
import           Stage
import           Term

check :: Recursive a => Annotated a -> Praxis (Annotated a)
check a = save stage $ do
  stage .= TypeCheck Warmup
  our .= initialSystem
  a' <- generate a
  (ts, ops) <- solve
  let solveTy   = \case { TyUni n   -> lookup n ts;  _ -> Nothing }
  let solveTyOp = \case { TyOpUni n -> lookup n ops; _ -> Nothing }
  r <- eval (sub solveTyOp (sub solveTy a'))
  display r `ifFlag` debug
  return r
  -- TODO type defaulting
