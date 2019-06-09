module Check.Kind.Require
  ( require
  , requires
  , newConstraint
  , implies
  , our
  ) where

import           Check.Kind.Reason
import           Check.Kind.System
import           Check.System      hiding (System)
import           Common
import           Introspect
import           Praxis
import           Term

require :: Kinded KindConstraint -> Praxis ()
require c = our . constraints %= (c:)

requires :: [Kinded KindConstraint] -> Praxis ()
requires = mapM_ require

newConstraint :: KindConstraint KindCheck -> Reason -> Source -> Kinded KindConstraint
newConstraint c r s = (s, Root (show r)) :< c

implies :: Kinded KindConstraint -> KindConstraint KindCheck -> Kinded KindConstraint
implies d c = let s = view source d in (s, Antecedent d) :< c

our :: Lens' PraxisState System
our = system . kindSystem
