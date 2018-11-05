module Check.Type.Require
  ( require
  , requires
  , newConstraint
  , implies
  , share
  , our
  ) where

import           Check.System          hiding (System)
import           Check.Type.Annotate
import           Check.Type.Constraint
import           Check.Type.System
import           Common
import           Praxis
import           Stage                 (TypeCheck)
import           Type

require :: Typed TypeConstraint -> Praxis ()
require c = system . typeSystem . constraints %= (c:)

requires :: [Typed TypeConstraint] -> Praxis ()
requires = mapM_ require

newConstraint :: TypeConstraint TypeCheck -> Reason -> Source -> Typed TypeConstraint
newConstraint c r s = (s, Derivation { _antecedent = Nothing, _reason = r }) :< c

implies :: Typed TypeConstraint -> TypeConstraint TypeCheck -> Typed TypeConstraint
implies d c = over annotation (set antecedent (Just d)) (set value c d)

share :: Typed Type -> TypeConstraint TypeCheck
share t = Class $ (Phantom, ()) :< TyApply ((Phantom, ()) :< TyCon "Share") t

our :: Lens' PraxisState System
our = system . typeSystem