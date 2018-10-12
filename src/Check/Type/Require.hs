module Check.Type.Require
  ( require
  , requires
  , newConstraint
  , implies
  , share
  ) where

import           Check.System
import           Check.Type.Annotate
import           Check.Type.Constraint
import           Check.Type.System
import           Common
import           Praxis
import           Source
import           Tag
import           Type

require :: Typed (Const Constraint) -> Praxis ()
require c = system . typeSystem . constraints %= (c:)

requires :: [Typed (Const Constraint)] -> Praxis ()
requires = mapM_ require

newConstraint :: Constraint -> Reason -> Source -> Typed (Const Constraint)
newConstraint c r s = (s, Derivation { origin = c, reason = r }) :< (Const c)

implies :: Typed (Const Constraint) -> Constraint -> Typed (Const Constraint)
implies d c = set value (Const c) d

share :: Typed Type -> Constraint
share t = Class $ (Phantom, ()) :< TyApply ((Phantom, ()) :< TyCon "Share") t
