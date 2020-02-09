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

require :: Annotated KindConstraint -> Praxis ()
require c = our . constraints %= (c:)

requires :: [Annotated KindConstraint] -> Praxis ()
requires = mapM_ require

newConstraint :: KindConstraint -> Reason -> Source -> Annotated KindConstraint
newConstraint c r s = (s, Just (Root (show r))) :< c

implies :: Annotated KindConstraint -> KindConstraint -> Annotated KindConstraint
implies d c = let s = view source d in (s, Just (Antecedent d)) :< c

our :: Lens' PraxisState System
our = system . kindSystem
