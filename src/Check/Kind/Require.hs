module Check.Kind.Require
  ( require
  , requires
  , newConstraint
  , implies
  , our
  ) where

import           Annotate
import           Check.Kind.Annotate
import           Check.Kind.Constraint
import           Check.Kind.System
import           Check.System          hiding (System)
import           Common
import           Control.Lens          (Lens')
import           Praxis
import           Source
import           Stage                 (KindCheck)
import           Tag
import           Type

require :: Kinded KindConstraint -> Praxis ()
require c = our . constraints %= (c:)

requires :: [Kinded KindConstraint] -> Praxis ()
requires = mapM_ require

newConstraint :: KindConstraint KindCheck -> Reason -> Source -> Kinded KindConstraint
newConstraint c r s = (s, Derivation { _antecedent = Nothing, _reason = r }) :< c

implies :: Kinded KindConstraint -> KindConstraint KindCheck -> Kinded KindConstraint
implies d c = over annotation (set antecedent (Just d)) (set value c d)

our :: Lens' PraxisState System
our = system . kindSystem
