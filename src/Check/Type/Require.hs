module Check.Type.Require
  ( require
  , requires
  , newConstraint
  , implies
  , share
  , our
  ) where

import           Check.System      hiding (System)
import           Check.Type.Reason
import           Check.Type.System
import           Common
import           Introspect
import           Praxis
import           Term

require :: Typed TypeConstraint -> Praxis ()
require c = our . constraints %= (c:)

requires :: [Typed TypeConstraint] -> Praxis ()
requires = mapM_ require

newConstraint :: TypeConstraint TypeCheck -> Reason -> Source -> Typed TypeConstraint
newConstraint c r s = (s, Root (show r)) :< c

implies :: Typed TypeConstraint -> TypeConstraint TypeCheck -> Typed TypeConstraint
implies d c = let s = view source d in (s, Antecedent d) :< c

share :: Typed Type -> TypeConstraint TypeCheck
share t = Class $ (Phantom, ()) :< TyApply ((Phantom, ()) :< TyCon "Share") t

our :: Lens' PraxisState System
our = system . typeSystem
