{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE StandaloneDeriving        #-}

module Introspect
  ( Visit(..)
  , skip
  , I(..)
  , Term(..)
  , retag
  , typeof
  , visit
  , introspect
  , embedVisit
  , embedSub
  , embedMonoid
  , sub
  , extract
  , extractPartial
  ) where

import           Common
import           Term

import           Data.Bitraversable (bitraverse)
import qualified Data.Set           as Set (fromList, toList)
import           GHC.Exts           (Constraint)

data Visit f a b = Visit (f a)
                 | Resolve (f b)

skip :: Applicative f => Visit f () a
skip = Visit (pure ())

class Term a where
  witness :: I a
  complete :: (Term a, Applicative f) => I a -> (forall a. Term a => Annotated a -> f (Annotated a)) -> Annotation a -> f (Annotation a)
  recurse :: Applicative f => (forall a. Term a => Annotated a -> f (Annotated a)) -> a -> f a

completion :: (Term a, Applicative f) => I a -> (forall a. Term a => Annotated a -> f (Annotated a)) -> Maybe (Annotation a) -> f (Maybe (Annotation a))
completion i f = \case
  Nothing -> pure Nothing
  Just x  -> Just <$> complete i f x

-- TODO Lit? Fixity?
data I a where
  -- | Operators
  IAssoc    :: I Assoc
  IOp       :: I Op
  IOpRules  :: I OpRules
  IPrec     :: I Prec
  -- | T0
  IDataAlt :: I DataAlt
  IDecl    :: I Decl
  IExp     :: I Exp
  IPat     :: I Pat
  IProgram :: I Program
  IStmt    :: I Stmt
  ITok     :: I Tok
  -- | T1
  ITyOp   :: I TyOp
  ITyPat  :: I TyPat
  IType   :: I Type
  IQType  :: I QType
  IQTyVar :: I QTyVar
  -- | T2
  IKind :: I Kind
  -- | Solver
  ITypeConstraint :: I TypeConstraint
  IKindConstraint :: I KindConstraint

typeof :: forall a. Term a => a -> I a
typeof _ = witness :: I a

switch :: forall a b c. (Term a, Term b) => I a -> I b -> ((a ~ b) => c) -> c -> c
switch a b eq neq = case (a, b) of
  -- | Operators
  (IAssoc, IAssoc)                   -> eq
  (IOp, IOp)                         -> eq
  (IOpRules, IOpRules)               -> eq
  (IPrec, IPrec)                     -> eq
  -- | T0
  (IDataAlt, IDataAlt)               -> eq
  (IDecl, IDecl)                     -> eq
  (IExp, IExp)                       -> eq
  (IPat, IPat)                       -> eq
  (IProgram, IProgram)               -> eq
  (IStmt, IStmt)                     -> eq
  (ITok, ITok)                       -> eq
  -- | T1
  (ITyOp, ITyOp)                     -> eq
  (ITyPat, ITyPat)                   -> eq
  (IType, IType)                     -> eq
  (IQType, IQType)                   -> eq
  (IQTyVar, IQTyVar)                 -> eq
  -- | T2
  (IKind, IKind)                     -> eq
  -- | Solver
  (ITypeConstraint, ITypeConstraint) -> eq
  (IKindConstraint, IKindConstraint) -> eq
  -- |
  _                                  -> neq

-- Apply a visitor through a term
visit :: (Term a, Applicative f) => (forall a. Term a => Annotated a -> Visit f (Maybe (Annotation a)) (Annotated a)) -> Annotated a -> f (Annotated a)
visit f x = case f x of
  Visit c   -> (\a' x' -> (view source x, a') :< x') <$> c <*> recurse (visit f) (view value x)
  Resolve r -> r

-- Apply a visitor through the term, including through annotations
introspect :: forall a f. (Term a, Applicative f) => (forall a. Term a => Annotated a -> Visit f () a) -> Annotated a -> f (Annotated a)
introspect f x = set annotation <$> completion (witness :: I a) (introspect f) (view annotation x) <*> ((\r -> set value r x) <$> case f x of
  Visit c   -> c *> recurse (introspect f) (view value x)
  Resolve r -> r
  )

embedVisit :: forall a f. (Term a, Applicative f) => (Annotated a -> Visit f () a) -> (forall b. Term b => Annotated b -> Visit f () b)
embedVisit f = g where
  g :: forall b. Term b => Annotated b -> Visit f () b
  g x = switch (witness :: I a) (witness :: I b) (f x) skip

transferA :: forall a b f. (Term a, Term b, Applicative f) => (a -> f a) -> b -> f b
transferA f x = switch (witness :: I a) (witness :: I b) (f x) (pure x)

transferM :: forall a b f. (Term a, Term b) => (a -> Maybe a) -> b -> Maybe b
transferM f x = switch (witness :: I a) (witness :: I b) (f x) Nothing

sub :: forall a. Term a => (forall b. Term b => b -> Maybe b) -> Annotated a -> Annotated a
sub f x = runIdentity $ introspect f' x where
  f' :: forall b. Term b => Annotated b -> Visit Identity () b
  f' y = case f (view value y) of
    Nothing -> Visit (Identity ())
    Just y' -> Resolve (Identity y')

extract :: forall a m. (Term a, Monoid m) => (forall b. Term b => b -> m) -> Annotated a -> m
extract f = extractPartial (\x -> (f x, True))

-- Similar to extract, but with control for whether or not to recurse
extractPartial :: forall a m. (Term a, Monoid m) => (forall b. Term b => b -> (m, Bool)) -> Annotated a -> m
extractPartial f x = getConst $ visit f' x where
  f' :: forall b. Term b => Annotated b -> Visit (Const m) (Maybe (Annotation b)) (Annotated b)
  f' y = case f (view value y) of
    (m, True)  -> Visit (Const m)
    (m, False) -> Resolve (Const m)

embedSub :: forall a b. Term a => (a -> Maybe a) -> (forall a. Term a => a -> Maybe a)
embedSub f x = transferM f x

embedMonoid :: forall a b. (Monoid b, Term a) => (a -> b) -> (forall a. Term a => a -> b)
embedMonoid f x = getConst $ transferA (Const . f) x

retag :: forall b. Term b => (forall a. Term a => I a -> Maybe (Annotation a) -> Maybe (Annotation a)) -> Annotated b -> Annotated b
retag f = runIdentity . visit f'
  where f' :: forall a. Term a => Annotated a -> Visit Identity (Maybe (Annotation a)) (Annotated a)
        f' x = Visit (Identity (f (witness :: I a) (view annotation x)))

-- Implementations below here

-- TODO use template haskell to generate recurse

trivial :: (Annotation a ~ Void, Term a, Applicative f) => I a -> (forall a. Term a => Annotated a -> f (Annotated a)) -> Annotation a -> f (Annotation a)
trivial _ _ = absurd

-- | Operators

instance Term Assoc where
  witness = IAssoc
  complete = trivial
  recurse _ = pure

instance Term Op where
  witness = IOp
  complete = trivial
  recurse _ = pure

instance Term OpRules where
  witness = IOpRules
  complete = trivial
  recurse f = \case
    OpRules a ps    -> OpRules <$> traverse f a <*> traverse f ps
    OpMultiRules rs -> OpMultiRules <$> traverse (bitraverse f (traverse f)) rs

instance Term Prec where
  witness = IPrec
  complete = trivial
  recurse _ = pure

-- | T0

instance Term DataAlt where
  witness = IDataAlt
  complete _ f (DataAltInfo ct args rt) = DataAltInfo <$> f ct <*> traverse f args <*> f rt
  recurse f = \case
    DataAlt n at -> DataAlt n <$> traverse f at

instance Term Decl where
  witness = IDecl
  complete = trivial
  recurse f = \case
    DeclData n t ts -> DeclData n <$> traverse f t <*> traverse f ts
    DeclFun n ps e  -> DeclFun n <$> traverse f ps <*> f e
    DeclOp o d rs   -> DeclOp <$> f o <*> pure d <*> f rs
    DeclSig n t     -> DeclSig n <$> f t
    DeclVar n t e   -> DeclVar n <$> traverse f t <*> f e

instance Term Exp where
  witness = IExp
  complete _ f x = f x
  recurse f = \case
    Apply a b    -> Apply <$> f a <*> f b
    Case a as    -> Case <$> f a <*> traverse (\(a, b) -> (,) <$> f a <*> f b) as
    Cases as     -> Cases <$> traverse (\(a, b) -> (,) <$> f a <*> f b) as
    Con n        -> pure (Con n)
    Do ss        -> Do <$> traverse f ss
    If a b c     -> If <$> f a <*> f b <*> f c
    Lambda a b   -> Lambda <$> f a <*> f b
    Lit l        -> pure (Lit l)
    Mixfix ts    -> Mixfix <$> traverse f ts
    Read n a     -> Read n <$> f a
    Pair a b     -> Pair <$> f a <*> f b
    Sig e t      -> Sig <$> f e <*> f t
    Unit         -> pure Unit
    Var n        -> pure (Var n)
    VarBang n    -> pure (VarBang n)

instance Term Pat where
  witness = IPat
  complete _ f x = f x
  recurse f = \case
    PatAt n a   -> PatAt n <$> f a
    PatCon n p  -> PatCon n <$> traverse f p
    PatHole     -> pure PatHole
    PatLit l    -> pure (PatLit l)
    PatPair a b -> PatPair <$> f a <*> f b
    PatUnit     -> pure PatUnit
    PatVar n    -> pure (PatVar n)

instance Term Program where
  witness = IProgram
  complete = trivial
  recurse f = \case
    Program ds -> Program <$> traverse f ds

instance Term Stmt where
  witness = IStmt
  complete = trivial
  recurse f = \case
    StmtDecl d -> StmtDecl <$> f d
    StmtExp e  -> StmtExp <$> f e

instance Term Tok where
  witness = ITok
  complete = trivial
  recurse f = \case
    TExp e -> TExp <$> f e
    TOp o  -> pure (TOp o)

-- | T1

instance Term TyOp where
  witness = ITyOp
  complete = trivial
  recurse f = \case
    TyOpUni n -> pure (TyOpUni n)
    TyOpBang  -> pure TyOpBang
    TyOpId    -> pure TyOpId
    TyOpVar n -> pure (TyOpVar n)

instance Term TyPat where
  witness = ITyPat
  complete _ f x = f x
  recurse f = \case
    TyPatVar n  -> pure (TyPatVar n)

instance Term Type where
  witness = IType
  complete _ f x = f x
  recurse f = \case
    TyUni n     -> pure (TyUni n)
    TyApply a b -> TyApply <$> f a <*> f b
    TyCon n     -> pure (TyCon n)
    TyFun a b   -> TyFun <$> f a <*> f b
    TyOp op t   -> TyOp <$> f op <*> f t
    TyPair a b  -> TyPair <$> f a <*> f b
    TyUnit      -> pure TyUnit
    TyVar n     -> pure (TyVar n)

instance Term QType where
  witness = IQType
  complete = trivial
  recurse f = \case
    Forall vs t -> Forall <$> pure vs <*> f t

instance Term QTyVar where
  witness = IQTyVar
  complete = trivial
  recurse _ = pure

-- | T2

instance Term Kind where
  witness = IKind
  complete = trivial
  recurse f = \case
    KindUni n      -> pure (KindUni n)
    KindConstraint -> pure KindConstraint
    KindFun a b    -> KindFun <$> f a <*> f b
    KindType       -> pure KindType

-- | Solver

instance Term TypeConstraint where
  witness = ITypeConstraint
  complete _ f = \case
    Root r       -> pure (Root r)
    Antecedent c -> Antecedent <$> f c
  recurse f = \case
    Class t   -> Class <$> f t
    Affine t  -> Affine <$> f t
    Share t   -> Share <$> f t
    TEq a b   -> TEq <$> f a <*> f b
    TOpEq a b -> pure (TOpEq a b)

instance Term KindConstraint where
  witness = IKindConstraint
  complete _ f = \case
    Root r       -> pure (Root r)
    Antecedent c -> Antecedent <$> f c
  recurse f = \case
    KEq a b -> KEq <$> f a <*> f b

