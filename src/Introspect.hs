{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE StandaloneDeriving        #-}

module Introspect
  ( source -- TODO should this be here
  , annotation -- TODO should this be here
  , Visit(..)
  , skip
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
  , cast
  ) where

import           Common
import           Term

import qualified Data.Set as Set (fromList, toList)
import           GHC.Exts (Constraint)

-- These lenses are a bit more general so we can use them in a piecewise way
-- (where the intermedite value has an annotation and value which don't commute)
source :: Functor f => (Source -> f Source) -> Tag (Source, a) b -> f (Tag (Source, a) b)
source = tag . first

annotation :: Functor f => (a -> f b) -> Tag (Source, a) c -> f (Tag (Source, b) c)
annotation = tag . second

data Visit f a b = Visit (f a)
                 | Resolve (f b)

skip :: Applicative f => Visit f () a
skip = Visit (pure ())

class Recursive a where
  witness :: I a
  recurse :: Applicative f => (forall a. Recursive a => Annotated s a -> f (Annotated t a)) -> a s -> f (a t)

class Complete s where
  complete :: (Recursive a, Applicative f) => (forall a. Recursive a => Annotated s a -> f (Annotated s a)) -> I a -> Annotation s a -> f (Annotation s a)

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

class Castable a s t where
  cast :: Annotated s a -> Annotated t a

instance Castable Kind Parse KindCheck where
  cast = retag f where
    f :: forall a. Recursive a => I a -> Annotation Parse a -> Annotation KindCheck a
    f i _ = case i of
      IKind -> ()

instance Castable Kind KindCheck TypeCheck where
  cast = retag f where
    f :: forall a. Recursive a => I a -> Annotation KindCheck a -> Annotation TypeCheck a
    f i _ = case i of
      IKind -> ()

instance Castable Type KindCheck TypeCheck where
  cast = retag f where
    f :: forall a. Recursive a => I a -> Annotation KindCheck a -> Annotation TypeCheck a
    f i k = case i of
      IType -> cast k

instance Castable QType KindCheck TypeCheck where
  cast = retag f where
    f :: forall a. Recursive a => I a -> Annotation KindCheck a -> Annotation TypeCheck a
    f i k = case i of
      IQType -> ()
      IType  -> cast k

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
    Mono t      -> Mono <$> f t
    Forall vs t -> Forall <$> pure vs <*> f t

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

instance Recursive TypeConstraint where
  witness = ITypeConstraint
  recurse f x = case x of
    Class t -> Class <$> f t
    TEq a b -> TEq <$> f a <*> f b

instance Recursive KindConstraint where
  witness = IKindConstraint
  recurse f x = case x of
    KEq a b -> KEq <$> f a <*> f b

instance Complete Parse where
  complete _ _ _ = pure ()

instance Complete KindCheck where
  complete f i a = case i of
    IDataAlt        -> pure ()
    IDecl           -> pure ()
    IExp            -> pure ()
    IKind           -> pure ()
    IPat            -> pure ()
    IProgram        -> pure ()
    IQType          -> pure ()
    IStmt           -> pure ()
    ITyPat          -> f a
    IType           -> f a
    ITypeConstraint -> pure ()
    IKindConstraint -> case a of { Root _ -> pure a; Antecedent a -> Antecedent <$> f a }

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
    ITyPat          -> pure a
    IType           -> pure a
    ITypeConstraint -> case a of { Root _ -> pure a; Antecedent a -> Antecedent <$> f a }
    IKindConstraint -> pure ()
