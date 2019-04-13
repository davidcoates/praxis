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
type instance Annotation KindCheck Kind = ()
type instance Annotation KindCheck Pat = Kinded Type
type instance Annotation KindCheck Program = ()
type instance Annotation KindCheck QType = () -- TODO Perhaps this should be Kind
type instance Annotation KindCheck Stmt = ()
type instance Annotation KindCheck TyPat = Kinded Kind
type instance Annotation KindCheck Type = Kinded Kind
type instance Annotation KindCheck TypeConstraint = ()
type instance Annotation KindCheck KindConstraint = Derivation
-- TODO can we use a default instance here? default as ()

instance Complete KindCheck where
  complete f i a = case i of
    IDataAlt        -> pure ()
    IDecl           -> pure ()
    IExp            -> f a
    IKind           -> pure ()
    IPat            -> f a
    IProgram        -> pure ()
    IQType          -> pure ()
    IStmt           -> pure ()
    ITyPat          -> pure a
    IType           -> pure a
    ITypeConstraint -> pure ()
    IKindConstraint -> case a of { Root _ -> pure a; Antecedent a -> Antecedent <$> f a }
  label t = let a = view annotation t in case typeof t of
    IExp            -> show a
    IPat            -> show a
    ITyPat          -> show a
    IType           -> show a
    IKindConstraint -> show a
    _               -> ""

