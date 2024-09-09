{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE Strict                #-}
{-# LANGUAGE StrictData            #-}
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


type TermAction f = forall a. Term a => Annotated a -> f (Annotated a)

class Term a where
  witness :: I a
  recurseTerm :: Applicative f => TermAction f -> a -> f a
  recurseAnnotation :: (Term a, Applicative f) => I a -> TermAction f -> Annotation a -> f (Annotation a)

recurse :: forall a f. (Term a, Applicative f) => TermAction f -> Annotated a -> f (Annotated a)
recurse f ((src, a) :< x) = (\a x -> (src, a) :< x) <$> traverse (recurseAnnotation (witness :: I a) f) a <*> recurseTerm f x

-- TODO Lit? Fixity?
data I a where
  -- | Operators
  IAssoc    :: I Assoc
  IOp       :: I Op
  IOpRules  :: I OpRules
  IPrec     :: I Prec
  -- | T0
  IBind     :: I Bind
  IDataCon  :: I DataCon
  IDecl     :: I Decl
  IDeclTerm :: I DeclTerm
  IDeclType :: I DeclType
  IExp      :: I Exp
  IPat      :: I Pat
  IProgram  :: I Program
  IStmt     :: I Stmt
  ITok      :: I Tok
  -- | T1
  IQType        :: I QType
  ITyConstraint :: I TyConstraint
  ITyOp         :: I TyOp
  IType         :: I Type
  ITyVar        :: I TyVar
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
  (IDeclTerm, IDeclTerm)               -> eq
  (IDeclType, IDeclType)               -> eq
  (IExp, IExp)                         -> eq
  (IPat, IPat)                         -> eq
  (IProgram, IProgram)                 -> eq
  (IStmt, IStmt)                       -> eq
  (ITok, ITok)                         -> eq
  -- | T1
  (IQType, IQType)                     -> eq
  (ITyConstraint, ITyConstraint)       -> eq
  (ITyOp, ITyOp)                       -> eq
  (IType, IType)                       -> eq
  (ITyVar, ITyVar)                     -> eq
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

trivial :: (Annotation a ~ Void, Term a, Applicative f) => I a -> TermAction f -> Annotation a -> f (Annotation a)
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
    OpRulesSweet rs -> OpRulesSweet <$> traverse (bitraverse f (traverse f)) rs

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
    DeclOpSweet o d rs -> DeclOpSweet <$> f o <*> pure d <*> f rs
    DeclSynSweet n t   -> DeclSynSweet n <$> f t
    DeclType d         -> DeclType <$> f d
    DeclTerm d         -> DeclTerm <$> f d

instance Term DeclTerm where
  witness = IDeclTerm
  recurseAnnotation = trivial
  recurseTerm f = \case
    DeclTermRec ds          -> DeclTermRec <$> traverse f ds
    DeclTermVar n t e       -> DeclTermVar n <$> traverse f t <*> f e
    DeclTermDefSweet n ps e -> DeclTermDefSweet n <$> traverse f ps <*> f e
    DeclTermSigSweet n t    -> DeclTermSigSweet n <$> f t

instance Term DeclType where
  witness = IDeclType
  recurseAnnotation _ f x = f x
  recurseTerm f = \case
    DeclTypeData m n t as -> DeclTypeData m n <$> traverse f t <*> traverse f as
    DeclTypeEnum n as     -> pure (DeclTypeEnum n as)


pair :: (Term a, Term b) => Applicative f => TermAction f -> (Annotated a, Annotated b) -> f (Annotated a, Annotated b)
pair f (a, b) = (,) <$> f a <*> f b

pairs :: (Term a, Term b) => Applicative f => TermAction f -> [(Annotated a, Annotated b)] -> f [(Annotated a, Annotated b)]
pairs f = traverse (pair f)

instance Term Exp where
  witness = IExp
  recurseAnnotation _ f x = f x
  recurseTerm f = \case
    Apply a b       -> Apply <$> f a <*> f b
    Case a as       -> Case <$> f a <*> pairs f as
    Cases as        -> Cases <$> pairs f as
    Closure cs e    -> Closure <$> traverse (second f) cs <*> f e
    Con n           -> pure (Con n)
    Defer a b       -> Defer <$> f a <*> f b
    DoSweet ss      -> DoSweet <$> traverse f ss
    If a b c        -> If <$> f a <*> f b <*> f c
    Lambda a b      -> Lambda <$> f a <*> f b
    Let a b         -> Let <$> f a <*> f b
    Lit l           -> pure (Lit l)
    MixfixSweet ts  -> MixfixSweet <$> traverse f ts
    Read n a        -> Read n <$> f a
    Pair a b        -> Pair <$> f a <*> f b
    Seq a b         -> Seq <$> f a <*> f b
    Sig e t         -> Sig <$> f e <*> f t
    Specialise e xs -> Specialise <$> f e <*> pairs f xs
    Switch as       -> Switch <$> pairs f as
    Unit            -> pure Unit
    Var n           -> pure (Var n)
    VarRefSweet n   -> pure (VarRefSweet n)
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
    TokExp e -> TokExp <$> f e
    TokOp o  -> pure (TokOp o)

-- | T1

instance Term QType where
  witness = IQType
  recurseAnnotation = trivial
  recurseTerm f = \case
    Forall vs cs t -> Forall <$> traverse f vs <*> traverse f cs <*> f t
    Mono t         -> Mono <$> f t

instance Term TyConstraint where
  witness = ITyConstraint
  recurseAnnotation = trivial
  recurseTerm f = \case
    HoldsInteger n t    -> HoldsInteger n <$> f t
    Instance t          -> Instance <$> f t
    Ref t               -> Ref <$> f t
    RefFree n t         -> RefFree n <$> f t
    TEq a b             -> TEq <$> f a <*> f b
    TOpEq a b           -> TOpEq <$> f a <*> f b
    TOpEqIfAffine a b t -> TOpEqIfAffine <$> f a <*> f b <*> f t

instance Term TyOp where
  witness = ITyOp
  recurseAnnotation _ f x = f x
  recurseTerm f = \case
    Multi os   -> Multi . Set.fromList <$> traverse f (Set.toList os)
    RefLabel n -> pure (RefLabel n)
    RefUni n   -> pure (RefUni n)
    RefVar n   -> pure (RefVar n)
    ViewUni n  -> pure (ViewUni n)
    ViewIdentity  -> pure ViewIdentity
    ViewVar n  -> pure (ViewVar n)

instance Term Type where
  witness = IType
  recurseAnnotation _ f x = f x
  recurseTerm f = \case
    TyApply a b -> TyApply <$> f a <*> f b
    TyCon n     -> pure (TyCon n)
    TyFn a b    -> TyFn <$> f a <*> f b
    TyOp o      -> TyOp <$> f o
    TyPair a b  -> TyPair <$> f a <*> f b
    TyUni n     -> pure (TyUni n)
    TyUnit      -> pure TyUnit
    TyVar n     -> pure (TyVar n)

instance Term TyVar where
  witness = ITyVar
  recurseAnnotation _ f x = f x
  recurseTerm f = pure

-- | T2

instance Term Kind where
  witness = IKind
  recurseAnnotation = trivial
  recurseTerm f = \case
    KindConstraint -> pure KindConstraint
    KindFn a b     -> KindFn <$> f a <*> f b
    KindRef        -> pure KindRef
    KindType       -> pure KindType
    KindUni n      -> pure (KindUni n)
    KindView       -> pure KindView

instance Term KindConstraint where
  witness = IKindConstraint
  recurseAnnotation = trivial
  recurseTerm f = \case
    KEq k l  -> KEq <$> f k <*> f l
    KPlain k -> KPlain <$> f k
    KSub k l -> KSub <$> f k <*> f l

-- | Solver

instance Term TyRequirement where
  witness = ITyRequirement
  recurseAnnotation _ f x = case x of
    TyReasonApply a b -> TyReasonApply <$> f a <*> f b
    TyReasonBind p e  -> TyReasonBind <$> f p <*> f e
    TyReasonRead n    -> pure (TyReasonRead n)
    -- TODO
    _                 -> pure x
  recurseTerm f = \case
    Requirement c -> Requirement <$> recurseTerm f c

instance Term KindRequirement where
  witness = IKindRequirement
  recurseAnnotation _ f x = case x of
    KindReasonData n a    -> KindReasonData n <$> traverse f a
    KindReasonDataCon c   -> KindReasonDataCon <$> f c
    KindReasonQType t     -> KindReasonQType <$> f t
    KindReasonTyApply a b -> KindReasonTyApply <$> f a <*> f b
    KindReasonType t      -> KindReasonType <$> f t
    KindReasonTyVar t     -> KindReasonTyVar <$> f t
  recurseTerm f = \case
    Requirement c -> Requirement <$> recurseTerm f c
