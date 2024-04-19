{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeOperators         #-}

module Introspect
  ( I(..)
  , Term(..)
  , recurse
  , typeof
  , embedSub
  , embedMonoid
  , sub
  , extract
  , deepExtract
  ) where

import           Common
import           Term

import           Data.Bitraversable (bitraverse)
import qualified Data.Set           as Set (fromList, toList)
import           GHC.Exts           (Constraint)


type Termformer f = forall a. Term a => Annotated a -> f (Annotated a)

class Term a where
  witness :: I a
  recurseTerm :: Applicative f => Termformer f -> a -> f a
  recurseAnnotation :: (Term a, Applicative f) => I a -> Termformer f -> Annotation a -> f (Annotation a)

recurse :: forall a f. (Term a, Applicative f) => Termformer f -> Annotated a -> f (Annotated a)
recurse f ((src, a) :< x) = (\a x -> (src, a) :< x) <$> traverse (recurseAnnotation (witness :: I a) f) a <*> recurseTerm f x

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
  IView         :: I View
  ITyPat        :: I TyPat
  IType         :: I Type
  ITyConstraint :: I TyConstraint
  IQType        :: I QType
  IQTyVar       :: I QTyVar
  -- | T2
  IKind           :: I Kind
  IKindConstraint :: I KindConstraint
  -- | Solver
  ITyRequirement   :: I TyRequirement
  IKindRequirement :: I KindRequirement


typeof :: forall a. Term a => a -> I a
typeof _ = witness :: I a

switch :: forall a b c. (Term a, Term b) => I a -> I b -> ((a ~ b) => c) -> c -> c
switch a b eq neq = case (a, b) of
  -- | Operators
  (IAssoc, IAssoc)                     -> eq
  (IOp, IOp)                           -> eq
  (IOpRules, IOpRules)                 -> eq
  (IPrec, IPrec)                       -> eq
  -- | T0
  (IBind, IBind)                       -> eq
  (IDataCon, IDataCon)                 -> eq
  (IDecl, IDecl)                       -> eq
  (IExp, IExp)                         -> eq
  (IPat, IPat)                         -> eq
  (IProgram, IProgram)                 -> eq
  (IStmt, IStmt)                       -> eq
  (ITok, ITok)                         -> eq
  -- | T1
  (IView, IView)                       -> eq
  (ITyPat, ITyPat)                     -> eq
  (IType, IType)                       -> eq
  (ITyConstraint, ITyConstraint)       -> eq
  (IQType, IQType)                     -> eq
  (IQTyVar, IQTyVar)                   -> eq
  -- | T2
  (IKind, IKind)                       -> eq
  (IKindConstraint, IKindConstraint)   -> eq
  -- | Solver
  (ITyRequirement, ITyRequirement)     -> eq
  (IKindRequirement, IKindRequirement) -> eq
  -- |
  _                                    -> neq


sub :: forall a. Term a => (forall b. Term b => Annotated b -> Maybe (Annotated b)) -> Annotated a -> Annotated a
sub f x = case f x of
  Just y  -> y
  Nothing -> runIdentity $ recurse (Identity . sub f) x

extract :: forall a m. (Term a, Monoid m) => (forall b. Term b => b -> m) -> Annotated a -> m
extract f (_ :< x) = f x <> (getConst $ recurseTerm (Const . extract f) x)

deepExtract :: forall a m. (Term a, Monoid m) => (forall b. Term b => b -> m) -> Annotated a -> m
deepExtract f x = f (view value x) <> (getConst $ recurse (Const . deepExtract f) x)

embedSub :: forall a. Term a => (Annotated a -> Maybe (Annotated a)) -> (forall b. Term b => Annotated b -> Maybe (Annotated b))
embedSub f x = transferM f x where
  transferM :: forall a b f. (Term a, Term b) => (Annotated a -> Maybe (Annotated a)) -> Annotated b -> Maybe (Annotated b)
  transferM f x = switch (witness :: I a) (witness :: I b) (f x) Nothing

embedMonoid :: forall a b. (Monoid b, Term a) => (a -> b) -> (forall a. Term a => a -> b)
embedMonoid f x = getConst $ transferA (Const . f) x where
  transferA :: forall a b f. (Term a, Term b, Applicative f) => (a -> f a) -> b -> f b
  transferA f x = switch (witness :: I a) (witness :: I b) (f x) (pure x)


-- Implementations below here

-- TODO use template haskell to generate recurseTerm

trivial :: (Annotation a ~ Void, Term a, Applicative f) => I a -> Termformer f -> Annotation a -> f (Annotation a)
trivial _ _ = absurd

-- | Operators

instance Term Assoc where
  witness = IAssoc
  recurseAnnotation = trivial
  recurseTerm _ = pure

instance Term Op where
  witness = IOp
  recurseAnnotation = trivial
  recurseTerm _ = pure

instance Term OpRules where
  witness = IOpRules
  recurseAnnotation = trivial
  recurseTerm f = \case
    OpRules a ps    -> OpRules <$> traverse f a <*> traverse f ps
    OpMultiRules rs -> OpMultiRules <$> traverse (bitraverse f (traverse f)) rs

instance Term Prec where
  witness = IPrec
  recurseAnnotation = trivial
  recurseTerm _ = pure

-- | T0

instance Term Bind where
  witness = IBind
  recurseAnnotation = trivial
  recurseTerm f = \case
    Bind a b -> Bind <$> f a <*> f b

instance Term DataCon where
  witness = IDataCon
  recurseAnnotation _ f x = f x
  recurseTerm f = \case
    DataCon n t -> DataCon n <$> f t

instance Term Decl where
  witness = IDecl
  recurseAnnotation = trivial
  recurseTerm f = \case
    DeclData m n t as -> DeclData m n <$> traverse f t <*> traverse f as
    DeclDef n ps e    -> DeclDef n <$> traverse f ps <*> f e
    DeclEnum n as     -> pure (DeclEnum n as)
    DeclOp o d rs     -> DeclOp <$> f o <*> pure d <*> f rs
    DeclRec ds        -> DeclRec <$> traverse f ds
    DeclSig n t       -> DeclSig n <$> f t
    DeclSyn n t       -> DeclSyn n <$> f t
    DeclVar n t e     -> DeclVar n <$> traverse f t <*> f e


pair :: (Term a, Term b) => Applicative f => Termformer f -> (Annotated a, Annotated b) -> f (Annotated a, Annotated b)
pair f (a, b) = (,) <$> f a <*> f b

pairs :: (Term a, Term b) => Applicative f => Termformer f -> [(Annotated a, Annotated b)] -> f [(Annotated a, Annotated b)]
pairs f = traverse (pair f)

instance Term Exp where
  witness = IExp
  recurseAnnotation _ f x = f x
  recurseTerm f = \case
    Apply a b       -> Apply <$> f a <*> f b
    Case a as       -> Case <$> f a <*> pairs f as
    Cases as        -> Cases <$> pairs f as
    Con n           -> pure (Con n)
    Defer a b       -> Defer <$> f a <*> f b
    Do ss           -> Do <$> traverse f ss
    If a b c        -> If <$> f a <*> f b <*> f c
    Lambda a b      -> Lambda <$> f a <*> f b
    Let a b         -> Let <$> f a <*> f b
    Lit l           -> pure (Lit l)
    Mixfix ts       -> Mixfix <$> traverse f ts
    Read n a        -> Read n <$> f a
    Pair a b        -> Pair <$> f a <*> f b
    Seq a b         -> Seq <$> f a <*> f b
    Sig e t         -> Sig <$> f e <*> f t
    Specialise e xs -> Specialise <$> f e <*> pairs f xs
    Switch as       -> Switch <$> pairs f as
    Unit            -> pure Unit
    Var n           -> pure (Var n)
    VarRef n        -> pure (VarRef n)
    Where a bs      -> Where <$> f a <*> traverse f bs

instance Term Pat where
  witness = IPat
  recurseAnnotation _ f x = f x
  recurseTerm f = \case
    PatAt n a   -> PatAt n <$> f a
    PatData n p -> PatData n <$> f p
    PatEnum n   -> pure (PatEnum n)
    PatHole     -> pure PatHole
    PatLit l    -> pure (PatLit l)
    PatPair a b -> PatPair <$> f a <*> f b
    PatUnit     -> pure PatUnit
    PatVar n    -> pure (PatVar n)

instance Term Program where
  witness = IProgram
  recurseAnnotation = trivial
  recurseTerm f = \case
    Program ds -> Program <$> traverse f ds

instance Term Stmt where
  witness = IStmt
  recurseAnnotation = trivial
  recurseTerm f = \case
    StmtBind b -> StmtBind <$> f b
    StmtExp e  -> StmtExp <$> f e

instance Term Tok where
  witness = ITok
  recurseAnnotation = trivial
  recurseTerm f = \case
    TExp e -> TExp <$> f e
    TOp o  -> pure (TOp o)

-- | T1

instance Term View where
  witness = IView
  recurseAnnotation _ f x = f x
  recurseTerm _ = pure

instance Term TyPat where
  witness = ITyPat
  recurseAnnotation _ f x = f x
  recurseTerm f = \case
    TyPatVar n       -> pure (TyPatVar n)
    TyPatViewVar d n -> pure (TyPatViewVar d n)
    TyPatPack a b    -> TyPatPack <$> f a <*> f b

instance Term Type where
  witness = IType
  recurseAnnotation _ f x = f x
  recurseTerm f = \case
    TyUni n     -> pure (TyUni n)
    TyApply a b -> TyApply <$> f a <*> f b
    TyCon n     -> pure (TyCon n)
    TyFun a b   -> TyFun <$> f a <*> f b
    TyView v    -> TyView <$> f v
    TyPack a b  -> TyPack <$> f a <*> f b
    TyPair a b  -> TyPair <$> f a <*> f b
    TyUnit      -> pure TyUnit
    TyVar n     -> pure (TyVar n)

instance Term TyConstraint where
  witness = ITyConstraint
  recurseAnnotation = trivial
  recurseTerm f = \case
    Class t      -> Class <$> f t
    RefFree n t  -> RefFree n <$> f t
    Copy t       -> Copy <$> f t
    TEq a b      -> TEq <$> f a <*> f b
    TOpEq a b    -> TOpEq <$> f a <*> f b

instance Term QType where
  witness = IQType
  recurseAnnotation = trivial
  recurseTerm f = \case
    Forall vs cs t -> Forall <$> traverse f vs <*> traverse f cs <*> f t

instance Term QTyVar where
  witness = IQTyVar
  recurseAnnotation _ f x = f x
  recurseTerm _ = pure

-- | T2

instance Term Kind where
  witness = IKind
  recurseAnnotation = trivial
  recurseTerm f = \case
    KindUni n      -> pure (KindUni n)
    KindConstraint -> pure KindConstraint
    KindFun a b    -> KindFun <$> f a <*> f b
    KindView d     -> pure (KindView d)
    KindPair a b   -> KindPair <$> f a <*> f b
    KindType       -> pure KindType

instance Term KindConstraint where
  witness = IKindConstraint
  recurseAnnotation = trivial
  recurseTerm f = \case
    KEq a b  -> KEq <$> f a <*> f b
    KSub a b -> KSub <$> f a <*> f b

-- | Solver

instance Term TyRequirement where
  witness = ITyRequirement
  recurseAnnotation _ f x = case x of
    TyReasonApply a b -> TyReasonApply <$> f a <*> f b
    TyReasonRead n    -> pure (TyReasonRead n)
    TyReasonBind p e  -> TyReasonBind <$> f p <*> f e
    -- TODO
    _ -> pure x
  recurseTerm f = \case
    Requirement c -> Requirement <$> recurseTerm f c

instance Term KindRequirement where
  witness = IKindRequirement
  recurseAnnotation _ f x = case x of
    KindReasonTyApply a b -> KindReasonTyApply <$> f a <*> f b
    KindReasonDataCon c   -> KindReasonDataCon <$> f c
    KindReasonData n a    -> KindReasonData n <$> traverse f a
    KindReasonType t      -> KindReasonType <$> f t
  recurseTerm f = \case
    Requirement c -> Requirement <$> recurseTerm f c
