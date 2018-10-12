module Check.Kind.Require
  ( require
  , requires
  , newConstraint
  , implies
  , our
  ) where

import           Check.Kind.Annotate
import           Check.Kind.Constraint
import           Check.Kind.System
import           Check.System          hiding (System)
import           Common
import           Control.Lens          (Lens')
import           Praxis
import           Source
import           Tag
import           Type

require :: Kinded (Const Constraint) -> Praxis ()
require c = our . constraints %= (c:)

requires :: [Kinded (Const Constraint)] -> Praxis ()
requires = mapM_ require

newConstraint :: Constraint -> Reason -> Source -> Kinded (Const Constraint)
newConstraint c r s = (s, Derivation { _origin = c, _reason = r }) :< (Const c)

implies :: Kinded (Const Constraint) -> Constraint -> Kinded (Const Constraint)
implies d c = set value (Const c) d

our :: Lens' PraxisState System
our = system . kindSystem
