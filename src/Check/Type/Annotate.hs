{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

module Check.Type.Annotate
  ( Typed
  )
  where

import           Check.Type.Constraint
import           Common
import           Introspect
import           Stage                 (TypeCheck)

type Typed a = Annotated TypeCheck a

-- TODO incomplete
-- TODO use records

type instance Annotation TypeCheck DataAlt = ()
type instance Annotation TypeCheck Decl = ()
type instance Annotation TypeCheck Exp = Typed Type
type instance Annotation TypeCheck Pat = Typed Type
type instance Annotation TypeCheck Program = ()
type instance Annotation TypeCheck QType = ()
type instance Annotation TypeCheck Stmt = ()
type instance Annotation TypeCheck TyPat = ()
type instance Annotation TypeCheck Type = ()
type instance Annotation TypeCheck TypeConstraint = Derivation
type instance Annotation TypeCheck KindConstraint = ()

instance Complete TypeCheck where
  complete f i a = case i of
    IDataAlt        -> pure ()
    IDecl           -> pure ()
    IExp            -> f a
    IPat            -> f a
    IProgram        -> pure ()
    IQType          -> pure ()
    IStmt           -> pure ()
    ITyPat          -> pure ()
    IType           -> pure ()
    ITypeConstraint -> case a of { Root _ -> pure a; Antecedent a -> Antecedent <$> f a }
    IKindConstraint -> pure ()
  label t = let a = view annotation t in case typeof t of
    IExp            -> show a
    IPat            -> show a
    ITypeConstraint -> show a
    _               -> ""
