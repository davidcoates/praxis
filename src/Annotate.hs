{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

module Annotate
  ( Derivation(..)
  , Parse
  , Parsed
  , TypeCheck
  , Typed
  , KindCheck
  , Kinded
  ) where

import           AST
import           Common
import           Introspect
import           Kind
import           Print
import           Type

data Derivation s a = Root String
                    | Antecedent (Annotated s a)

instance Show (Annotated s a) => Show (Derivation s a) where
  show (Root r)       = "\n|-> (" ++ show r ++ ")"
  show (Antecedent a) = "\n|-> " ++ show a

data Parse
type Parsed a = Annotated Parse a

type instance Annotation Parse a = ()

instance Complete Parse where
  complete _ _ _ = pure ()

data TypeCheck
type Typed a = Annotated TypeCheck a

type instance Annotation TypeCheck DataAlt = ()
type instance Annotation TypeCheck Decl = ()
type instance Annotation TypeCheck Exp = Typed Type
type instance Annotation TypeCheck Kind = ()
type instance Annotation TypeCheck Pat = Typed Type
type instance Annotation TypeCheck Program = ()
type instance Annotation TypeCheck QType = ()
type instance Annotation TypeCheck Stmt = ()
type instance Annotation TypeCheck TyPat = ()
type instance Annotation TypeCheck Type = ()
type instance Annotation TypeCheck Type.Constraint = Derivation TypeCheck Type.Constraint
type instance Annotation TypeCheck Kind.Constraint = ()

instance Complete TypeCheck where
  complete f i a = case i of
    IDataAlt        -> pure ()
    IDecl           -> pure ()
    IExp            -> f a
    IKind           -> pure ()
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

data KindCheck
type Kinded a = Annotated KindCheck a

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
type instance Annotation KindCheck Type.Constraint = ()
type instance Annotation KindCheck Kind.Constraint = Derivation KindCheck Kind.Constraint
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
