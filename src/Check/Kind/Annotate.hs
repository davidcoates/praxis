{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

module Check.Kind.Annotate
  ( Kinded
  )
  where

import           Check.Kind.Constraint
import           Common
import           Introspect
import           Stage                 (KindCheck)
import           Type                  (Kind)

type Kinded a = Annotated KindCheck a

-- TODO incomplete
-- TODO use records

type instance Annotation KindCheck DataAlt = ()
type instance Annotation KindCheck Decl = ()
type instance Annotation KindCheck Exp = Kinded Type
type instance Annotation KindCheck Pat = Kinded Type
type instance Annotation KindCheck Program = ()
type instance Annotation KindCheck QType = () -- TODO Perhaps this should be Kind
type instance Annotation KindCheck Stmt = ()
type instance Annotation KindCheck TyPat = Kind
type instance Annotation KindCheck Type = Kind
type instance Annotation KindCheck TypeConstraint = ()
type instance Annotation KindCheck KindConstraint = Derivation

instance Complete KindCheck where
  complete f i a = case i of
    IDataAlt        -> pure ()
    IDecl           -> pure ()
    IExp            -> f a
    IPat            -> f a
    IProgram        -> pure ()
    IQType          -> pure ()
    IStmt           -> pure ()
    ITyPat          -> pure a
    IType           -> pure a
    ITypeConstraint -> pure ()
    IKindConstraint -> antecedent (series . (f <$>)) a
