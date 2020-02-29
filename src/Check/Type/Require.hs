module Check.Type.Require
  ( require
  , requires
  , newConstraint
  , implies
  , our
  ) where

import           Check.System      hiding (System)
import           Check.Type.Reason
import           Check.Type.System
import           Common
import           Introspect
import           Praxis
import           Term

require :: Annotated TypeConstraint -> Praxis ()
require c = our . constraints %= (c:)

requires :: [Annotated TypeConstraint] -> Praxis ()
requires = mapM_ require

newConstraint :: TypeConstraint -> Reason -> Source -> Annotated TypeConstraint
newConstraint c r s = (s, Just (Root (show r))) :< c

implies :: Annotated TypeConstraint -> TypeConstraint -> Annotated TypeConstraint
implies d c = let s = view source d in (s, Just (Antecedent d)) :< c

our :: Lens' PraxisState System
our = system . typeSystem
