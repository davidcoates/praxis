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
  , Recursive(..)
  , retag
  , typeof
  , visit
  , introspect
  , embedVisit
  , embedMonoid
  , sub
  , extract
  ) where

import           Common
import           Term

import qualified Data.Set as Set (fromList, toList)
import           GHC.Exts (Constraint)

data Visit f a b = Visit (f a)
                 | Resolve (f b)

skip :: Applicative f => Visit f () a
skip = Visit (pure ())

class Recursive a where
  witness :: I a
  complete :: (Recursive a, Applicative f) => I a -> (forall a. Recursive a => Annotated a -> f (Annotated a)) -> Annotation a -> f (Annotation a)
  recurse :: Applicative f => (forall a. Recursive a => Annotated a -> f (Annotated a)) -> a -> f a

completion :: (Recursive a, Applicative f) => I a -> (forall a. Recursive a => Annotated a -> f (Annotated a)) -> Maybe (Annotation a) -> f (Maybe (Annotation a))
completion i f = \case
  Nothing -> pure Nothing
  Just x  -> Just <$> complete i f x

data I a where
  IDataAlt :: I DataAlt
  IDecl    :: I Decl
  IExp     :: I Exp
  IKind    :: I Kind
  IPat     :: I Pat
  IProgram :: I Program
  IQType   :: I QType
  IStmt    :: I Stmt
  ITok     :: I Tok
  ITyOp    :: I TyOp
  ITyPat   :: I TyPat
  IType    :: I Type
  ITypeConstraint :: I TypeConstraint
  IKindConstraint :: I KindConstraint

typeof :: forall a. Recursive a => Annotated a -> I a
typeof _ = witness :: I a

switch :: forall a b c. (Recursive a, Recursive b) => I a -> I b -> ((a ~ b) => c) -> c -> c
switch a b eq neq = case (a, b) of
  (IDataAlt, IDataAlt)               -> eq
  (IDecl, IDecl)                     -> eq
  (IExp, IExp)                       -> eq
  (IKind, IKind)                     -> eq
  (IPat, IPat)                       -> eq
  (IProgram, IProgram)               -> eq
  (IQType, IQType)                   -> eq
  (IStmt, IStmt)                     -> eq
  (ITok, ITok)                       -> eq
  (ITyOp, ITyOp)                     -> eq
  (ITyPat, ITyPat)                   -> eq
  (IType, IType)                     -> eq
  (ITypeConstraint, ITypeConstraint) -> eq
  (IKindConstraint, IKindConstraint) -> eq
  _                                  -> neq

visit :: (Recursive a, Applicative f) => (forall a. Recursive a => Annotated a -> Visit f (Maybe (Annotation a)) (Annotated a)) -> Annotated a -> f (Annotated a)
visit f x = case f x of
  Visit c   -> (\a' x' -> (view source x, a') :< x') <$> c <*> recurse (visit f) (view value x)
  Resolve r -> r

introspect :: (Recursive a, Applicative f) => (forall a. Recursive a => Annotated a -> Visit f () a) -> Annotated a -> f (Annotated a)
introspect f x = set annotation <$> completion (typeof x) (introspect f) (view annotation x) <*> ((\r -> set value r x) <$> case f x of
  Visit c   -> c *> recurse (introspect f) (view value x)
  Resolve r -> r
  )

embedVisit :: forall a f. (Recursive a, Applicative f) => (Annotated a -> Visit f () a) -> (forall b. Recursive b => Annotated b -> Visit f () b)
embedVisit f = g where
  g :: forall b. Recursive b => Annotated b -> Visit f () b
  g x = switch (witness :: I a) (witness :: I b) (f x) skip

transferA :: forall a b f. (Recursive a, Recursive b, Applicative f) => (a -> f a) -> b -> f b
transferA f x = switch (witness :: I a) (witness :: I b) (f x) (pure x)

transferM :: forall a b f. (Recursive a, Recursive b) => (a -> Maybe a) -> b -> Maybe b
transferM f x = switch (witness :: I a) (witness :: I b) (f x) Nothing

sub :: forall a b s. (Recursive a, Recursive b) => (a -> Maybe a) -> Annotated b -> Annotated b
sub f x = runIdentity $ introspect f' x where
  f' :: forall a. Recursive a => Annotated a -> Visit Identity () (a)
  f' y = case transferM f (view value y) of
    Nothing -> Visit (Identity ())
    Just y' -> Resolve (Identity y')

extract :: forall a b. (Monoid b, Recursive a) => (forall a. Recursive a => Annotated a -> b) -> Annotated a -> b
extract f x = getConst $ introspect f' x where
  f' :: forall a. Recursive a => Annotated a -> Visit (Const b) () (a)
  f' y = Visit (Const (f y))

embedMonoid :: forall a b. (Monoid b, Recursive a) => (a -> b) -> (forall a. Recursive a => Annotated a -> b)
embedMonoid f x = getConst $ transferA (Const . f) (view value x)

retag :: forall b. Recursive b => (forall a. Recursive a => I a -> Maybe (Annotation a) -> Maybe (Annotation a)) -> Annotated b -> Annotated b
retag f = runIdentity . visit f'
  where f' :: forall a. Recursive a => Annotated a -> Visit Identity (Maybe (Annotation a)) (Annotated a)
        f' x = Visit (Identity (f (typeof x) (view annotation x)))

-- Implementations below here

-- TODO use template haskell to generate recurse

trivial :: (Annotation a ~ Void, Recursive a, Applicative f) => I a -> (forall a. Recursive a => Annotated a -> f (Annotated a)) -> Annotation a -> f (Annotation a)
trivial _ _ = absurd

instance Recursive DataAlt where
  witness = IDataAlt
  complete _ f (DataAltInfo ns ct args rt) = DataAltInfo ns <$> f ct <*> traverse f args <*> f rt
  recurse f = \case
    DataAlt n t -> DataAlt n <$> traverse f t

instance Recursive Decl where
  witness = IDecl
  complete = trivial
  recurse f = \case
    DeclData n t ts -> DeclData n <$> series (f <$> t) <*> traverse f ts
    DeclFun n ps e  -> DeclFun n <$> traverse f ps <*> f e
    DeclSig n t     -> DeclSig n <$> f t
    DeclVar n t e   -> DeclVar n <$> series (f <$> t) <*> f e

instance Recursive Exp where
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
    Record r     -> Record <$> traverse f r
    Sig e t      -> Sig <$> f e <*> f t
    Var n        -> pure (Var n)
    VarBang n    -> pure (VarBang n)

instance Recursive Kind where
  witness = IKind
  complete = trivial
  recurse f = \case
    KindUni n      -> pure (KindUni n)
    KindConstraint -> pure KindConstraint
    KindFun a b    -> KindFun <$> f a <*> f b
    KindType       -> pure KindType

instance Recursive Pat where
  witness = IPat
  complete _ f x = f x
  recurse f = \case
    PatAt n a   -> PatAt n <$> f a
    PatHole     -> pure PatHole
    PatLit l    -> pure (PatLit l)
    PatRecord r -> PatRecord <$> traverse f r
    PatVar n    -> pure (PatVar n)
    PatCon n ps -> PatCon n <$> traverse f ps

instance Recursive Program where
  witness = IProgram
  complete = trivial
  recurse f = \case
    Program ds -> Program <$> traverse f ds

instance Recursive Stmt where
  witness = IStmt
  complete = trivial
  recurse f = \case
    StmtDecl d -> StmtDecl <$> f d
    StmtExp e  -> StmtExp <$> f e

instance Recursive QType where
  witness = IQType
  complete = trivial
  recurse f = \case
    Mono t      -> Mono <$> f t
    Forall vs t -> Forall <$> pure vs <*> f t

instance Recursive Tok where
  witness = ITok
  complete = trivial
  recurse f = \case
    TExp e -> TExp <$> f e
    TOp o  -> pure (TOp o)

instance Recursive TyOp where
  witness = ITyOp
  complete = trivial
  recurse f = \case
    TyOpUni n -> pure (TyOpUni n)
    TyOpBang  -> pure TyOpBang
    TyOpId    -> pure TyOpId
    TyOpVar n -> pure (TyOpVar n)

instance Recursive TyPat where
  witness = ITyPat
  complete _ f x = f x
  recurse f = \case
    TyPatVar n  -> pure (TyPatVar n)

instance Recursive Type where
  witness = IType
  complete _ f x = f x
  recurse f = \case
    TyUni n     -> pure (TyUni n)
    TyApply a b -> TyApply <$> f a <*> f b
    TyCon n     -> pure (TyCon n)
    TyFlat ts   -> TyFlat <$> (Set.fromList <$> traverse f (Set.toList ts))
    TyFun a b   -> TyFun <$> f a <*> f b
    TyRecord r  -> TyRecord <$> traverse f r
    TyOp op t   -> TyOp <$> f op <*> f t
    TyVar n     -> pure (TyVar n)

instance Recursive TypeConstraint where
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

instance Recursive KindConstraint where
  witness = IKindConstraint
  complete _ f = \case
    Root r       -> pure (Root r)
    Antecedent c -> Antecedent <$> f c
  recurse f = \case
    KEq a b -> KEq <$> f a <*> f b
