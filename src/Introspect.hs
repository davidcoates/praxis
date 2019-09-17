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
  , Complete(..)
  , typeof
  , visit
  , introspect
  , just
  , sub
  , extract
  , only
  , retag
  , cast
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
  recurse :: Applicative f => (forall a. Recursive a => Annotated s a -> f (Annotated t a)) -> a s -> f (a t)

class Complete s where
  complete :: (Recursive a, Applicative f) => (forall a. Recursive a => Annotated s a -> f (Annotated s a)) -> Annotation s a -> I a -> f (Annotation s a)

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
  (ITyOp, ITyOp)                     -> eq
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
introspect f x = set annotation <$> complete (introspect f) (view annotation x) (typeof x) <*> ((\r -> set value r x) <$> case f x of
  Visit c   -> c *> recurse (introspect f) (view value x)
  Resolve r -> r
  )

just :: forall a s f. (Recursive a, Applicative f) => (Annotated s a -> Visit f () (a s)) -> (forall b. Recursive b => Annotated s b -> Visit f () (b s))
just f = g where
  g :: forall b. Recursive b => Annotated s b -> Visit f () (b s)
  g x = switch (witness :: I a) (witness :: I b) (f x) skip

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

retag :: forall s t b. Recursive b => (forall a. Recursive a => I a -> Annotation s a -> Annotation t a) -> Annotated s b -> Annotated t b
retag f = runIdentity . visit f'
  where f' :: forall a. Recursive a => Annotated s a -> Visit Identity (Annotation t a) (Annotated t a)
        f' x = Visit (Identity (f (typeof x) (view annotation x)))

-- TODO this cast stuff is gross REALLY FUCKING GROSS PLEASE FIX THANK
class Castable a s t where
  cast :: Annotated s a -> Annotated t a

instance (Annotation s TyOp ~ Annotation t TyOp) => Castable TyOp s t where
  cast = retag f where
    f :: forall a. Recursive a => I a -> Annotation s a -> Annotation t a
    f i x = case i of
      ITyOp -> x

instance (Annotation s Kind ~ Annotation t Kind) => Castable Kind s t where
  cast = retag f where
    f :: forall a. Recursive a => I a -> Annotation s a -> Annotation t a
    f i x = case i of
      IKind -> x

instance Castable Type KindAnn TypeAnn where
  cast = retag f where
    f :: forall a. Recursive a => I a -> Annotation KindAnn a -> Annotation TypeAnn a
    f i k = case i of
      IType -> cast k

instance Castable QType KindAnn TypeAnn where
  cast = retag f where
    f :: forall a. Recursive a => I a -> Annotation KindAnn a -> Annotation TypeAnn a
    f i k = case i of
      IQType -> ()
      IType  -> cast k

instance Castable TyPat KindAnn TypeAnn where
  cast = retag f where
    f :: forall a. Recursive a => I a -> Annotation KindAnn a -> Annotation TypeAnn a
    f i k = case i of
      ITyPat -> cast k

-- Implementations below here

-- TODO use template haskell to generate recurse

instance Recursive DataAlt where
  witness = IDataAlt
  recurse f = \case
    DataAlt n t -> DataAlt n <$> traverse f t

instance Recursive Decl where
  witness = IDecl
  recurse f = \case
    DeclData n t ts -> DeclData n <$> series (f <$> t) <*> traverse f ts
    DeclFun n ps e  -> DeclFun n <$> traverse f ps <*> f e
    DeclSig n t     -> DeclSig n <$> f t
    DeclVar n t e   -> DeclVar n <$> series (f <$> t) <*> f e

instance Recursive Exp where
  witness = IExp
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
  recurse f = \case
    KindUni n      -> pure (KindUni n)
    KindConstraint -> pure KindConstraint
    KindFun a b    -> KindFun <$> f a <*> f b
    KindType       -> pure KindType

instance Recursive Pat where
  witness = IPat
  recurse f = \case
    PatAt n a   -> PatAt n <$> f a
    PatHole     -> pure PatHole
    PatLit l    -> pure (PatLit l)
    PatRecord r -> PatRecord <$> traverse f r
    PatVar n    -> pure (PatVar n)
    PatCon n ps -> PatCon n <$> traverse f ps

instance Recursive Program where
  witness = IProgram
  recurse f = \case
    Program ds -> Program <$> traverse f ds

instance Recursive Stmt where
  witness = IStmt
  recurse f = \case
    StmtDecl d -> StmtDecl <$> f d
    StmtExp e  -> StmtExp <$> f e

instance Recursive QType where
  witness = IQType
  recurse f = \case
    Mono t      -> Mono <$> f t
    Forall vs t -> Forall <$> pure vs <*> f t

instance Recursive Tok where
  witness = ITok
  recurse f = \case
    TExp e -> TExp <$> f e
    TOp o  -> pure (TOp o)

instance Recursive TyOp where
  witness = ITyOp
  recurse f = \case
    TyOpUni n -> pure (TyOpUni n)
    TyOpBang  -> pure TyOpBang
    TyOpId    -> pure TyOpId
    TyOpVar n -> pure (TyOpVar n)

instance Recursive TyPat where
  witness = ITyPat
  recurse f = \case
    TyPatVar n  -> pure (TyPatVar n)

instance Recursive Type where
  witness = IType
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
  recurse f = \case
    Class t -> Class <$> f t
    TEq a b -> TEq <$> f a <*> f b
    TOpEq a b -> pure (TOpEq a b)

instance Recursive KindConstraint where
  witness = IKindConstraint
  recurse f = \case
    KEq a b -> KEq <$> f a <*> f b

instance Complete SimpleAnn where
  complete _ _ _ = pure ()

instance Complete KindAnn where
  complete f a = \case
    IDataAlt        -> pure ()
    IDecl           -> pure ()
    IExp            -> pure ()
    IKind           -> pure ()
    IPat            -> pure ()
    IProgram        -> pure ()
    IQType          -> pure ()
    IStmt           -> pure ()
    ITyOp           -> pure ()
    ITyPat          -> f a
    IType           -> f a
    ITypeConstraint -> pure ()
    IKindConstraint -> case a of { Root _ -> pure a; Antecedent a -> Antecedent <$> f a }

instance Complete TypeAnn where
  complete f a = \case
    IDataAlt        -> case a of { DataAltInfo ns ct args rt -> DataAltInfo ns <$> f ct <*> traverse f args <*> f rt }
    IDecl           -> pure ()
    IExp            -> f a
    IKind           -> pure ()
    IPat            -> f a
    IProgram        -> pure ()
    IQType          -> pure ()
    IStmt           -> pure ()
    ITyOp           -> pure ()
    ITyPat          -> pure a
    IType           -> pure a
    ITypeConstraint -> case a of { Root _ -> pure a; Antecedent a -> Antecedent <$> f a }
    IKindConstraint -> pure ()
