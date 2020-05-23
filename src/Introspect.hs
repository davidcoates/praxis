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
  , embedSub
  , embedMonoid
  , sub
  , extract
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

-- TODO rename this to Term or some such
class Recursive a where
  witness :: I a
  complete :: (Recursive a, Applicative f) => I a -> (forall a. Recursive a => Annotated a -> f (Annotated a)) -> Annotation a -> f (Annotation a)
  recurse :: Applicative f => (forall a. Recursive a => Annotated a -> f (Annotated a)) -> a -> f a

completion :: (Recursive a, Applicative f) => I a -> (forall a. Recursive a => Annotated a -> f (Annotated a)) -> Maybe (Annotation a) -> f (Maybe (Annotation a))
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

typeof :: forall a. Recursive a => a -> I a
typeof _ = witness :: I a

switch :: forall a b c. (Recursive a, Recursive b) => I a -> I b -> ((a ~ b) => c) -> c -> c
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

visit :: (Recursive a, Applicative f) => (forall a. Recursive a => Annotated a -> Visit f (Maybe (Annotation a)) (Annotated a)) -> Annotated a -> f (Annotated a)
visit f x = case f x of
  Visit c   -> (\a' x' -> (view source x, a') :< x') <$> c <*> recurse (visit f) (view value x)
  Resolve r -> r

introspect :: forall a f. (Recursive a, Applicative f) => (forall a. Recursive a => Annotated a -> Visit f () a) -> Annotated a -> f (Annotated a)
introspect f x = set annotation <$> completion (witness :: I a) (introspect f) (view annotation x) <*> ((\r -> set value r x) <$> case f x of
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

sub :: forall a. Recursive a => (forall b. Recursive b => b -> Maybe b) -> Annotated a -> Annotated a
sub f x = runIdentity $ introspect f' x where
  f' :: forall b. Recursive b => Annotated b -> Visit Identity () b
  f' y = case f (view value y) of
    Nothing -> Visit (Identity ())
    Just y' -> Resolve (Identity y')

extract :: forall a m. (Recursive a, Monoid m) => (forall b. Recursive b => b -> m) -> Annotated a -> m
extract f x = getConst $ introspect f' x where
  f' :: forall b. Recursive b => Annotated b -> Visit (Const m) () b
  f' y = Visit (Const (f (view value y)))

embedSub :: forall a b. Recursive a => (a -> Maybe a) -> (forall a. Recursive a => a -> Maybe a)
embedSub f x = transferM f x

embedMonoid :: forall a b. (Monoid b, Recursive a) => (a -> b) -> (forall a. Recursive a => a -> b)
embedMonoid f x = getConst $ transferA (Const . f) x

retag :: forall b. Recursive b => (forall a. Recursive a => I a -> Maybe (Annotation a) -> Maybe (Annotation a)) -> Annotated b -> Annotated b
retag f = runIdentity . visit f'
  where f' :: forall a. Recursive a => Annotated a -> Visit Identity (Maybe (Annotation a)) (Annotated a)
        f' x = Visit (Identity (f (witness :: I a) (view annotation x)))

-- Implementations below here

-- TODO use template haskell to generate recurse

trivial :: (Annotation a ~ Void, Recursive a, Applicative f) => I a -> (forall a. Recursive a => Annotated a -> f (Annotated a)) -> Annotation a -> f (Annotation a)
trivial _ _ = absurd

-- | Operators

instance Recursive Assoc where
  witness = IAssoc
  complete = trivial
  recurse _ = pure

instance Recursive Op where
  witness = IOp
  complete = trivial
  recurse _ = pure

instance Recursive OpRules where
  witness = IOpRules
  complete = trivial
  recurse f = \case
    OpRules a ps    -> OpRules <$> traverse f a <*> traverse f ps
    OpMultiRules rs -> OpMultiRules <$> traverse (bitraverse f (traverse f)) rs

instance Recursive Prec where
  witness = IPrec
  complete = trivial
  recurse _ = pure

-- | T0

instance Recursive DataAlt where
  witness = IDataAlt
  complete _ f (DataAltInfo ns ct args rt) = DataAltInfo ns <$> f ct <*> traverse f args <*> f rt
  recurse f = \case
    DataAlt n t -> DataAlt n <$> traverse f t

instance Recursive Decl where
  witness = IDecl
  complete = trivial
  recurse f = \case
    DeclData n t ts -> DeclData n <$> traverse f t <*> traverse f ts
    DeclFun n ps e  -> DeclFun n <$> traverse f ps <*> f e
    DeclOp o d rs   -> DeclOp <$> f o <*> pure d <*> f rs
    DeclSig n t     -> DeclSig n <$> f t
    DeclVar n t e   -> DeclVar n <$> traverse f t <*> f e

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

instance Recursive Tok where
  witness = ITok
  complete = trivial
  recurse f = \case
    TExp e -> TExp <$> f e
    TOp o  -> pure (TOp o)

-- | T1

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
    TyFun a b   -> TyFun <$> f a <*> f b
    TyRecord r  -> TyRecord <$> traverse f r
    TyOp op t   -> TyOp <$> f op <*> f t
    TyVar n     -> pure (TyVar n)

instance Recursive QType where
  witness = IQType
  complete = trivial
  recurse f = \case
    Mono t      -> Mono <$> f t
    Forall vs t -> Forall <$> pure vs <*> f t

instance Recursive QTyVar where
  witness = IQTyVar
  complete = trivial
  recurse _ = pure

-- | T2

instance Recursive Kind where
  witness = IKind
  complete = trivial
  recurse f = \case
    KindUni n      -> pure (KindUni n)
    KindConstraint -> pure KindConstraint
    KindFun a b    -> KindFun <$> f a <*> f b
    KindType       -> pure KindType

-- | Solver

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

