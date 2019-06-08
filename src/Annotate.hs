{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

module Annotate
  ( Parse
  , TypeCheck
  , KindCheck
  , Annotation
  , Annotated
  , Parsed
  , Typed
  , Kinded
  , Derivation(..)
  ) where

import           AST
import           Common
import           Introspect
import           Kind
import           Print
import           Type

data Parse
data TypeCheck
data KindCheck

type family Annotation a (b :: * -> *) where
  -- | Parse
  Annotation Parse     a               = ()
  -- | TypeCheck
  Annotation TypeCheck Exp             = Typed Type
  Annotation TypeCheck Pat             = Typed Type
  Annotation TypeCheck Type.Constraint = Derivation TypeCheck Type.Constraint
  Annotation TypeCheck a               = ()
  -- | KindCheck
  Annotation KindCheck Exp             = Kinded Type
  Annotation KindCheck Pat             = Kinded Type
  Annotation KindCheck TyPat           = Kinded Kind
  Annotation KindCheck Type            = Kinded Kind
  Annotation KindCheck Kind.Constraint = Derivation KindCheck Kind.Constraint
  Annotation KindCheck a               = ()

type Annotated a b = Tag (Source, Annotation a b) (b a)

type Parsed a = Annotated Parse     a
type Typed  a = Annotated TypeCheck a
type Kinded a = Annotated KindCheck a

-- TODO should this be somewhere else?
data Derivation s a = Root String
                    | Antecedent (Annotated s a)

instance Pretty (Annotated s a) => Pretty (Derivation s a) where
  pretty (Root r)       = "\n|-> (" <> plain r <> ")"
  pretty (Antecedent a) = "\n|-> " <> pretty a

instance Complete Parse where
  complete _ _ _ = pure ()

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
    IExp            -> pretty a
    IPat            -> pretty a
    ITypeConstraint -> pretty a
    _               -> Nil

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
    IExp            -> pretty a
    IPat            -> pretty a
    ITyPat          -> pretty a
    IType           -> pretty a
    IKindConstraint -> pretty a
    _               -> Nil

