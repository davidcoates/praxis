{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE ScopedTypeVariables       #-}

module Introspect
  ( Analysis(..)
  , Intro
  , Omni
  , I(..)
  , Recursive(..)
  , Complete(..)
  , typeof
  , introspect
  , omnispect
  , sub
  , extract
  , only
  , asub
  , DataAlt
  , Decl
  , Exp
  , Pat
  , Program
  , QType
  , Stmt
  , TyPat
  , Type
  , TypeConstraint
  , KindConstraint
  ) where

import qualified Data.Set              as Set (fromList, toList)

import           AST
import           Check.Kind.Constraint (KindConstraint (..))
import           Check.Type.Constraint (TypeConstraint (..))
import           Common
import           Type

data Analysis f a b = Realise (f a)
                    | Notice (f b)

class Recursive a where
  witness :: I a
  recurse :: Applicative f => (forall a. Recursive a => Annotated s a -> f (Annotated t a)) -> a s -> f (a t)

class Complete s where
  complete :: (Recursive a, Applicative f) => (forall a. Recursive a => Annotated s a -> f (Annotated s a)) -> I a -> Annotation s a -> f (Annotation s a)

data I a where
  IDataAlt :: I DataAlt
  IDecl    :: I Decl
  IExp     :: I Exp
  IPat     :: I Pat
  IProgram :: I Program
  IQType   :: I QType
  IStmt    :: I Stmt
  ITyPat   :: I TyPat
  IType    :: I Type
  ITypeConstraint :: I TypeConstraint
  IKindConstraint :: I KindConstraint

typeof :: forall a s. Recursive a => Annotated s a -> I a
typeof _ = witness :: I a

transfer :: forall a b f s. (Recursive a, Recursive b, Applicative f) => (a s -> f (a s)) -> b s -> f (b s)
transfer f x = switch (witness :: I a) (witness :: I b) (f x) (pure x)

switch :: forall a b c. (Recursive a, Recursive b) => I a -> I b -> ((a ~ b) => c) -> c -> c
switch a b eq neq = case (a, b) of
  (IDataAlt, IDataAlt)               -> eq
  (IDecl, IDecl)                     -> eq
  (IExp, IExp)                       -> eq
  (IPat, IPat)                       -> eq
  (IProgram, IProgram)               -> eq
  (IQType, IQType)                   -> eq
  (IStmt, IStmt)                     -> eq
  (ITyPat, ITyPat)                   -> eq
  (IType, IType)                     -> eq
  (ITypeConstraint, ITypeConstraint) -> eq
  (IKindConstraint, IKindConstraint) -> eq
  _                                  -> neq

type Intro f s a = Analysis f (Annotated s a) (Annotation s a)

introspect :: forall f s t a. (Recursive a, Applicative f) => (forall a. Recursive a => Annotated s a -> Intro f t a) -> Annotated s a -> f (Annotated t a)
introspect f x = case f x of
  Realise r -> r
  Notice c  -> (\a' x' -> (view source x, a') :< x') <$> c <*> recurse (introspect f) (view value x)

type Omni f s a = Analysis f (a s) ()

omnispect :: forall f s a. (Recursive a, Applicative f, Complete s) => (forall a. Recursive a => Annotated s a -> Omni f s a) -> Annotated s a -> f (Annotated s a)
omnispect f x = set annotation <$> complete (omnispect f) (typeof x) (view annotation x) <*> ((\r -> set value r x) <$> case f x of
  Realise r -> r
  Notice c  -> c *> recurse (omnispect f) (view value x)
  )

sub :: forall a b s. (Recursive a, Recursive b, Complete s) => (a s -> Maybe (a s)) -> Annotated s b -> Annotated s b
sub f x = runIdentity $ omnispect f' x where
  f' :: forall a. Recursive a => Annotated s a -> Omni Identity s a
  f' y = case transfer f (view value y) of
    Nothing -> Notice (Identity ())
    Just y' -> Realise (Identity y')

extract :: forall a b s. (Monoid b, Recursive a, Complete s) => (forall a. Recursive a => Annotated s a -> b) -> Annotated s a -> b
extract f x = getConst $ omnispect f' x where
  f' :: forall a. Recursive a => Annotated s a -> Omni (Const b) s a
  f' y = Notice (Const (f y))

only :: forall a b s. (Monoid b, Recursive a) => (a s -> b) -> (forall a. Recursive a => Annotated s a -> b)
only f x = getConst $ transfer (Const . f) (view value x)

-- sub over annotations
asub :: forall a b s. (Recursive a, Recursive b, Complete s) => I a -> (Annotation s a -> Maybe (Annotation s a)) -> Annotated s b -> Annotated s b
asub i f x = set annotation a' $ over value (runIdentity . recurse (Identity . asub i f)) x
  where a = view annotation x
        a' :: Annotation s b
        a' = switch i (typeof x) (case f a of { Nothing -> a''; Just a' -> a' }) a''
        a'' :: Annotation s b
        a'' = runIdentity . complete f' (typeof x) $ a
        f' :: forall a. Recursive a => Annotated s a -> Identity (Annotated s a)
        f' = Identity . asub i f

-- Implementations below here

instance Recursive DataAlt where
  witness = IDataAlt
  recurse f x = case x of
    DataAlt n t -> DataAlt n <$> f t

instance Recursive Decl where
  witness = IDecl
  recurse f x = case x of
    DeclVar n t e -> DeclVar n <$> series ((\(a, b) -> (,) <$> f a <*> f b) <$> t) <*> f e
    DeclData n t ts -> DeclData n <$> series (f <$> t) <*> traverse f ts

instance Recursive Exp where
  witness = IExp
  recurse f x = case x of
    Apply a b    -> Apply <$> f a <*> f b
    Case a as    -> Case <$> f a <*> traverse (\(a, b) -> (,) <$> f a <*> f b) as
    Do ss        -> Do <$> traverse f ss
    If a b c     -> If <$> f a <*> f b <*> f c
    Lambda a b   -> Lambda <$> f a <*> f b
    Lit l        -> pure (Lit l)
    Read n a     -> Read n <$> f a
    Record r     -> Record <$> traverse f r
    Sig e (a, b) -> Sig <$> f e <*> ((,) <$> f a <*> f b)
    Var n        -> pure (Var n)

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
    Forall ks a b -> Forall ks <$> f a <*> f b
    QTyUni n      -> pure (QTyUni n)

instance Recursive TyPat where
  witness = ITyPat
  recurse f x = case x of
    TyPatVar n  -> pure (TyPatVar n)
    TyPatPack r -> TyPatPack <$> traverse f r

instance Recursive Type where
  witness = IType
  recurse f x = case x of
    TyUni n      -> pure (TyUni n)
    TyApply a b  -> TyApply <$> f a <*> f b
    TyBang a     -> TyBang <$> f a
    TyCon n      -> pure (TyCon n)
    TyFlat ts    -> TyFlat <$> (Set.fromList <$> traverse f (Set.toList ts))
    TyLambda a b -> TyLambda <$> f a <*> f b
    TyPack r     -> TyPack <$> traverse f r
    TyRecord r   -> TyRecord <$> traverse f r
    TyVar n      -> pure (TyVar n)

instance Recursive TypeConstraint where
  witness = ITypeConstraint
  recurse f x = case x of
    Class t                      -> Class <$> f t
    Check.Type.Constraint.Eq a b -> Check.Type.Constraint.Eq <$> f a <*> f b
    Generalises q t              -> Generalises <$> f q <*> f t
    Specialises t q              -> Specialises <$> f t <*> f q

instance Recursive KindConstraint where
  witness = IKindConstraint
  recurse f x = case x of
    Check.Kind.Constraint.Eq a b -> pure $ Check.Kind.Constraint.Eq a b
