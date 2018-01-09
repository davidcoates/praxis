module Checker.Solver
  ( solve
  ) where

import Checker.Constraint (Constraint(..))
import qualified Checker.Constraint as C (share, drop)
import Checker.TCMonad
import Checker.Constraint
import AST
import Type hiding (Constraint)

solve :: [Constraint] -> TC [Type]
solve _ = undefined
