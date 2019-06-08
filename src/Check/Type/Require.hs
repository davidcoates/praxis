module Check.Type.Require
  ( require
  , requires
  , newConstraint
  , implies
  , share
  , our
  ) where

import           Annotate
import           Check.System      hiding (System)
import           Check.Type.Reason
import           Check.Type.System
import           Common
import           Introspect
import           Praxis
import           Type

require :: Typed Constraint -> Praxis ()
require c = our . constraints %= (c:)

requires :: [Typed Constraint] -> Praxis ()
requires = mapM_ require

newConstraint :: Constraint TypeCheck -> Reason -> Source -> Typed Constraint
newConstraint c r s = (s, Root (show r)) :< c

implies :: Typed Constraint -> Constraint TypeCheck -> Typed Constraint
implies d c = let s = view source d in (s, Antecedent d) :< c

share :: Typed Type -> Constraint TypeCheck
share t = Class $ (Phantom, ()) :< TyApply ((Phantom, ()) :< TyCon "Share") t

our :: Lens' PraxisState System
our = system . typeSystem
