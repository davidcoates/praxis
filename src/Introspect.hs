{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NamedFieldPuns            #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TypeOperators             #-}

module Introspect
  ( Visit(..)
  , skip
  , I(..)
  , Term(..)
  , typeof
  , visit
  , introspect
  , embedVisit
  , embedSub
  , embedMonoid
  , sub
  , extract
  , extractPartial
  , deepExtract
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
  IBind    :: I Bind
  IDataCon :: I DataCon
  IDecl    :: I Decl
  IExp     :: I Exp
  IPat     :: I Pat
  IProgram :: I Program
  IStmt    :: I Stmt
  ITok     :: I Tok
  -- | T1
  IView   :: I View
  ITyPat  :: I TyPat
  IType   :: I Type
  IQType  :: I QType
  IQTyVar :: I QTyVar
  -- | T2
  IKind :: I Kind
  -- | Solver
  ITyConstraint :: I TyConstraint
  IKindConstraint :: I KindConstraint
  ITyProp :: I TyProp
  IKindProp :: I KindProp


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
  (IBind, IBind)                     -> eq
  (IDataCon, IDataCon)               -> eq
  (IDecl, IDecl)                     -> eq
  (IExp, IExp)                       -> eq
  (IPat, IPat)                       -> eq
  (IProgram, IProgram)               -> eq
  (IStmt, IStmt)                     -> eq
  (ITok, ITok)                       -> eq
  -- | T1
  (IView, IView)                     -> eq
  (ITyPat, ITyPat)                   -> eq
  (IType, IType)                     -> eq
  (IQType, IQType)                   -> eq
  (IQTyVar, IQTyVar)                 -> eq
  -- | T2
  (IKind, IKind)                     -> eq
  -- | Solver
  (ITyConstraint, ITyConstraint)     -> eq
  (IKindConstraint, IKindConstraint) -> eq
  (ITyProp, ITyProp)                 -> eq
  (IKindProp, IKindProp)             -> eq
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

deepExtract :: forall a m. (Term a, Monoid m) => (forall b. Term b => b -> m) -> Annotated a -> m
deepExtract f x = getConst $ introspect f' x where
  f' :: forall c. Term c => Annotated c -> Visit (Const m) () c
  f' y = Visit (Const (f (view value y)))

embedSub :: forall a b. Term a => (a -> Maybe a) -> (forall a. Term a => a -> Maybe a)
embedSub f x = transferM f x

embedMonoid :: forall a b. (Monoid b, Term a) => (a -> b) -> (forall a. Term a => a -> b)
embedMonoid f x = getConst $ transferA (Const . f) x

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

instance Term Bind where
  witness = IBind
  complete = trivial
  recurse f = \case
    Bind a b -> Bind <$> f a <*> f b

instance Term DataCon where
  witness = IDataCon
  complete _ f (DataConInfo { fullType, argType, retType }) = (\fullType argType retType -> DataConInfo { fullType, argType, retType}) <$> f fullType <*> traverse f argType <*> f retType
  recurse f = \case
    DataCon n at -> DataCon n <$> traverse f at

instance Term Decl where
  witness = IDecl
  complete = trivial
  recurse f = \case
    DeclData n t ts -> DeclData n <$> traverse f t <*> traverse f ts
    DeclFun n ps e  -> DeclFun n <$> traverse f ps <*> f e
    DeclOp o d rs   -> DeclOp <$> f o <*> pure d <*> f rs
    DeclSig n t     -> DeclSig n <$> f t
    DeclSyn n t     -> DeclSyn n <$> f t
    DeclVar n t e   -> DeclVar n <$> traverse f t <*> f e


pair :: (Term a, Term b) => Applicative f => (forall a. Term a => Annotated a -> f (Annotated a)) -> (Annotated a, Annotated b) -> f (Annotated a, Annotated b)
pair f (a, b) = (,) <$> f a <*> f b

pairs :: (Term a, Term b) => Applicative f => (forall a. Term a => Annotated a -> f (Annotated a)) -> [(Annotated a, Annotated b)] -> f [(Annotated a, Annotated b)]
pairs f = traverse (pair f)

instance Term Exp where
  witness = IExp
  complete _ f x = f x
  recurse f = \case
    Apply a b    -> Apply <$> f a <*> f b
    Case a as    -> Case <$> f a <*> pairs f as
    Cases as     -> Cases <$> pairs f as
    Con n        -> pure (Con n)
    Do ss        -> Do <$> traverse f ss
    If a b c     -> If <$> f a <*> f b <*> f c
    Lambda a b   -> Lambda <$> f a <*> f b
    Let a b      -> Let <$> f a <*> f b
    Lit l        -> pure (Lit l)
    Mixfix ts    -> Mixfix <$> traverse f ts
    Read n a     -> Read n <$> f a
    Pair a b     -> Pair <$> f a <*> f b
    Sig e t      -> Sig <$> f e <*> f t
    Switch as    -> Switch <$> pairs f as
    Unit         -> pure Unit
    Var n        -> pure (Var n)
    VarRef n     -> pure (VarRef n)
    Where a bs   -> Where <$> f a <*> traverse f bs

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
    StmtBind b -> StmtBind <$> f b
    StmtExp e  -> StmtExp <$> f e

instance Term Tok where
  witness = ITok
  complete = trivial
  recurse f = \case
    TExp e -> TExp <$> f e
    TOp o  -> pure (TOp o)

-- | T1

instance Term View where
  witness = IView
  complete = trivial
  recurse _ = pure

instance Term TyPat where
  witness = ITyPat
  complete _ f x = f x
  recurse f = \case
    TyPatVar n     -> pure (TyPatVar n)
    TyPatOpVar d n -> pure (TyPatOpVar d n)
    TyPatPack a b  -> TyPatPack <$> f a <*> f b

instance Term Type where
  witness = IType
  complete _ f x = f x
  recurse f = \case
    TyUni n     -> pure (TyUni n)
    TyApply a b -> TyApply <$> f a <*> f b
    TyCon n     -> pure (TyCon n)
    TyFun a b   -> TyFun <$> f a <*> f b
    View op     -> View <$> f op
    TyPack a b  -> TyPack <$> f a <*> f b
    TyPair a b  -> TyPair <$> f a <*> f b
    TyUnit      -> pure TyUnit
    TyVar n     -> pure (TyVar n)

instance Term QType where
  witness = IQType
  complete = trivial
  recurse f = \case
    Forall vs cs t -> Forall <$> traverse f vs <*> traverse f cs <*> f t

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
    KindView         -> pure KindView
    KindPair a b   -> KindPair <$> f a <*> f b
    KindType       -> pure KindType

-- | Solver

instance Term TyConstraint where
  witness = ITyConstraint
  complete = trivial
  recurse f = \case
    Class t      -> Class <$> f t
    RefFree n t  -> RefFree n <$> f t
    Share t      -> Share <$> f t
    TEq a b      -> TEq <$> f a <*> f b
    TOpEq a b    -> TOpEq <$> f a <*> f b

instance Term KindConstraint where
  witness = IKindConstraint
  complete = trivial
  recurse f = \case
    KEq a b -> KEq <$> f a <*> f b

instance Term TyProp where
  witness = ITyProp
  complete _ f = \case
    Root r       -> pure (Root r)
    Antecedent c -> Antecedent <$> f c
  recurse f = \case
    Top       -> pure Top
    Bottom    -> pure Bottom
    Exactly c -> Exactly <$> covalue f c
    And p1 p2 -> And <$> covalue f p1 <*> covalue f p2

instance Term KindProp where
  witness = IKindProp
  complete _ f = \case
    Root r       -> pure (Root r)
    Antecedent c -> Antecedent <$> f c
  recurse f = \case
    Top       -> pure Top
    Bottom    -> pure Bottom
    Exactly c -> Exactly <$> covalue f c
    And p1 p2 -> And <$> covalue f p1 <*> covalue f p2
