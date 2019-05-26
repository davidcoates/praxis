{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE StandaloneDeriving        #-}

module Introspect
  ( Visit(..)
  , I(..)
  , Recursive(..)
  , Complete(..)
  , typeof
  , visit
  , introspect
  , sub
  , extract
  , only
  , asub
  , retag
  ) where

import qualified Data.Set as Set (fromList, toList)

import           AST
import           Common
import           Kind
import           Type

data Visit f a b = Visit (f a)
                 | Resolve (f b)

class Recursive a where
  witness :: I a
  recurse :: Applicative f => (forall a. Recursive a => Annotated s a -> f (Annotated t a)) -> a s -> f (a t)

class Complete s where
  complete :: (Recursive a, Applicative f) => (forall a. Recursive a => Annotated s a -> f (Annotated s a)) -> I a -> Annotation s a -> f (Annotation s a)
  label :: Recursive a => Annotated s a -> Colored String
  label _ = Nil

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
  ITyPat   :: I TyPat
  IType    :: I Type
  ITypeConstraint :: I Type.Constraint
  IKindConstraint :: I Kind.Constraint

typeof :: forall a s. Recursive a => Annotated s a -> I a
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
  (ITyPat, ITyPat)                   -> eq
  (IType, IType)                     -> eq
  (ITypeConstraint, ITypeConstraint) -> eq
  (IKindConstraint, IKindConstraint) -> eq
  _                                  -> neq

visit :: (Recursive a, Applicative f) => (forall a. Recursive a => Annotated s a -> Visit f (Annotation t a) (Annotated t a)) -> Annotated s a -> f (Annotated t a)
visit f x = case f x of
  Visit c   -> (\a' x' -> (view source x, a') :< x') <$> c <*> recurse (visit f) (view value x)
  Resolve r -> r

introspect :: (Recursive a, Applicative f, Complete s) => (forall a. Recursive a => Annotated s a -> Visit f () (a s)) -> Annotated s a -> f (Annotated s a)
introspect f x = set annotation <$> complete (introspect f) (typeof x) (view annotation x) <*> ((\r -> set value r x) <$> case f x of
  Visit c   -> c *> recurse (introspect f) (view value x)
  Resolve r -> r
  )

transferA :: forall a b f s. (Recursive a, Recursive b, Applicative f) => (a s -> f (a s)) -> b s -> f (b s)
transferA f x = switch (witness :: I a) (witness :: I b) (f x) (pure x)

transferM :: forall a b f s. (Recursive a, Recursive b) => (a s -> Maybe (a s)) -> b s -> Maybe (b s)
transferM f x = switch (witness :: I a) (witness :: I b) (f x) Nothing

sub :: forall a b s. (Recursive a, Recursive b, Complete s) => (a s -> Maybe (a s)) -> Annotated s b -> Annotated s b
sub f x = runIdentity $ introspect f' x where
  f' :: forall a. Recursive a => Annotated s a -> Visit Identity () (a s)
  f' y = case transferM f (view value y) of
    Nothing -> Visit (Identity ())
    Just y' -> Resolve (Identity y')

extract :: forall a b s. (Monoid b, Recursive a, Complete s) => (forall a. Recursive a => Annotated s a -> b) -> Annotated s a -> b
extract f x = getConst $ introspect f' x where
  f' :: forall a. Recursive a => Annotated s a -> Visit (Const b) () (a s)
  f' y = Visit (Const (f y))

only :: forall a b s. (Monoid b, Recursive a) => (a s -> b) -> (forall a. Recursive a => Annotated s a -> b)
only f x = getConst $ transferA (Const . f) (view value x)

-- | Substitue over annotations
asub :: forall a b s. (Recursive a, Recursive b, Complete s) => I a -> (Annotation s a -> Maybe (Annotation s a)) -> Annotated s b -> Annotated s b
asub i f x = set annotation a' $ over value (runIdentity . recurse (Identity . asub i f)) x
  where a = view annotation x
        a' :: Annotation s b
        a' = switch i (typeof x) (case f a of { Nothing -> a''; Just a' -> a' }) a''
        a'' :: Annotation s b
        a'' = runIdentity . complete f' (typeof x) $ a
        f' :: forall a. Recursive a => Annotated s a -> Identity (Annotated s a)
        f' = Identity . asub i f

retag :: forall s t b. Recursive b => (forall a. Recursive a => I a -> Annotation s a -> Annotation t a) -> Annotated s b -> Annotated t b
retag f = runIdentity . visit f'
  where f' :: forall a. Recursive a => Annotated s a -> Visit Identity (Annotation t a) (Annotated t a)
        f' x = Visit (Identity (f (typeof x) (view annotation x)))

-- Implementations below here

-- TODO use template haskell to generate recurse

instance Recursive DataAlt where
  witness = IDataAlt
  recurse f x = case x of
    DataAlt n t -> DataAlt n <$> f t

instance Recursive Decl where
  witness = IDecl
  recurse f x = case x of
    DeclData n t ts -> DeclData n <$> series (f <$> t) <*> traverse f ts
    DeclFun n ps e  -> DeclFun n <$> traverse f ps <*> f e
    DeclSig n t     -> DeclSig n <$> f t
    DeclVar n t e   -> DeclVar n <$> series (f <$> t) <*> f e

instance Recursive Exp where
  witness = IExp
  recurse f x = case x of
    Apply a b    -> Apply <$> f a <*> f b
    Case a as    -> Case <$> f a <*> traverse (\(a, b) -> (,) <$> f a <*> f b) as
    Cases as     -> Cases <$> traverse (\(a, b) -> (,) <$> f a <*> f b) as
    Do ss        -> Do <$> traverse f ss
    If a b c     -> If <$> f a <*> f b <*> f c
    Lambda a b   -> Lambda <$> f a <*> f b
    Lit l        -> pure (Lit l)
    Mixfix ts    -> Mixfix <$> traverse f ts
    Read n a     -> Read n <$> f a
    Record r     -> Record <$> traverse f r
    Sig e t      -> Sig <$> f e <*> f t
    Var n        -> pure (Var n)
    VarBang n    -> pure (Var n)

instance Recursive Kind where
  witness = IKind
  recurse f x = case x of
    KindUni n      -> pure (KindUni n)
    KindConstraint -> pure KindConstraint
    KindFun a b    -> KindFun <$> f a <*> f b
    KindRecord r   -> KindRecord <$> traverse f r
    KindType       -> pure KindType

instance Recursive Pat where
  witness = IPat
  recurse f x = case x of
    PatAt n a   -> PatAt n <$> f a
    PatHole     -> pure PatHole
    PatLit l    -> pure (PatLit l)
    PatRecord r -> PatRecord <$> traverse f r
    PatVar n    -> pure (PatVar n)

instance Recursive Program where
  witness = IProgram
  recurse f x = case x of
    Program ds -> Program <$> traverse f ds

instance Recursive Stmt where
  witness = IStmt
  recurse f x = case x of
    StmtDecl d -> StmtDecl <$> f d
    StmtExp e  -> StmtExp <$> f e

instance Recursive QType where
  witness = IQType
  recurse f x = case x of
    Mono t        -> Mono <$> f t
    Forall ks a b -> Forall <$> traverse (second f) ks <*> f a <*> f b

instance Recursive Tok where
  witness = ITok
  recurse f x = case x of
    TExp e -> TExp <$> f e
    TOp o  -> pure (TOp o)

instance Recursive TyPat where
  witness = ITyPat
  recurse f x = case x of
    TyPatVar n  -> pure (TyPatVar n)
    TyPatPack r -> TyPatPack <$> traverse f r

instance Recursive Type where
  witness = IType
  recurse f x = case x of
    TyUni n     -> pure (TyUni n)
    TyApply a b -> TyApply <$> f a <*> f b
    TyBang a    -> TyBang <$> f a
    TyCon n     -> pure (TyCon n)
    TyFlat ts   -> TyFlat <$> (Set.fromList <$> traverse f (Set.toList ts))
    TyFun a b   -> TyFun <$> f a <*> f b
    TyPack r    -> TyPack <$> traverse f r
    TyRecord r  -> TyRecord <$> traverse f r
    TyVar n     -> pure (TyVar n)

instance Recursive Type.Constraint where
  witness = ITypeConstraint
  recurse f x = case x of
    Class t     -> Class <$> f t
    Type.Eq a b -> Type.Eq <$> f a <*> f b

instance Recursive Kind.Constraint where
  witness = IKindConstraint
  recurse f x = case x of
    Kind.Eq a b -> Kind.Eq <$> f a <*> f b
