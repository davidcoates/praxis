module Check.Kind.Require
  ( require
  , requires
  , newConstraint
  , implies
  , our
  ) where

import           Annotate
import           Check.Kind.Reason
import           Check.Kind.System
import           Check.System      hiding (System)
import           Common
import           Introspect
import           Kind
import           Praxis

require :: Kinded Constraint -> Praxis ()
require c = our . constraints %= (c:)

requires :: [Kinded Constraint] -> Praxis ()
requires = mapM_ require

newConstraint :: Constraint KindCheck -> Reason -> Source -> Kinded Constraint
newConstraint c r s = (s, Root (show r)) :< c

implies :: Kinded Constraint -> Constraint KindCheck -> Kinded Constraint
implies d c = let s = view source d in (s, Antecedent d) :< c

our :: Lens' PraxisState System
our = system . kindSystem
