module Check.Type.Require
  ( require
  , requires
  , newConstraint
  , implies
  , share
  , affine
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

-- TODO Share should be taken out of the environment so we don't have to kind it
share :: Annotated Type -> TypeConstraint
share t = Class $ TyApply (TyCon "Share" `as` phantom (KindFun (phantom KindType) (phantom KindConstraint))) t `as` phantom KindConstraint

-- TODO Affine should be taken out of the environment so we don't have to kind it
affine :: Annotated Type -> TypeConstraint
affine t = Class $ TyApply (TyCon "Affine" `as` phantom (KindFun (phantom KindType) (phantom KindConstraint))) t `as` phantom KindConstraint

our :: Lens' PraxisState System
our = system . typeSystem
