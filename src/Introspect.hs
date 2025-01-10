{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE Strict                #-}
{-# LANGUAGE StrictData            #-}
{-# LANGUAGE TypeOperators         #-}


module Introspect
  ( TermT(..)
  , IsTerm(..)
  , recurse
  , cast
  , typeof
  , embedSub
  , embedMonoid
  , sub
  , extract
  , deepExtract
  ) where

import           Common
import           Stage
import           Term

import           Data.Bitraversable (bitraverse)
import qualified Data.Set           as Set (fromList, toList)
import           GHC.Exts           (Constraint)


type TermAction f s t = forall a. IsTerm a => Annotated s a -> f (Annotated t a)

class IsTerm a where
  witness :: TermT a
  recurseTerm :: Applicative f => TermAction f s t -> a s -> f (a t)
  recurseAnnotation :: (Applicative f, IsTerm a, IsStage s) => StageT s -> TermT a -> TermAction f s s -> Annotation s a -> f (Annotation s a)

recurse :: forall a f s t. (Applicative f, IsTerm a, IsStage s) => TermAction f s s -> Annotated s a -> f (Annotated s a)
recurse f ((src, a) :< x) = (\a x -> (src, a) :< x) <$> traverse (recurseAnnotation (stageT :: StageT s) (witness :: TermT a) f) a <*> recurseTerm f x

cast :: forall a s t. IsTerm a => Annotated s a -> Annotated t a
cast ((src, _) :< term) = (src, Nothing) :< runIdentity (recurseTerm (Identity . cast) term)

-- TODO Lit? Fixity?
data TermT a where
  -- | Operators
  OpT       :: TermT Op
  OpRulesT  :: TermT OpRules
  PrecT     :: TermT Prec
  -- | T0
  BindT     :: TermT Bind
  DataConT  :: TermT DataCon
  DeclT     :: TermT Decl
  DeclRecT  :: TermT DeclRec
  DeclTermT :: TermT DeclTerm
  DeclTypeT :: TermT DeclType
  ExpT      :: TermT Exp
  PatT      :: TermT Pat
  ProgramT  :: TermT Program
  StmtT     :: TermT Stmt
  TokT      :: TermT Tok
  -- | T1
  QTypeT          :: TermT QType
  TypeConstraintT :: TermT TypeConstraint
  TypeT           :: TermT Type
  TypePatT        :: TermT TypePat
  -- | T2
  KindT           :: TermT Kind
  KindConstraintT :: TermT KindConstraint
  -- | Solver
  TypeRequirementT :: TermT (Requirement TypeConstraint)
  KindRequirementT :: TermT (Requirement KindConstraint)

deriving instance Show (TermT a)

typeof :: forall a (s :: Stage). IsTerm a => (a s) -> TermT a
typeof _ = witness :: TermT a

switch :: forall a b c. (IsTerm a, IsTerm b) => TermT a -> TermT b -> ((a ~ b) => c) -> c -> c
switch a b eq neq = case (a, b) of
  -- | Operators
  (OpT, OpT)                           -> eq
  (OpRulesT, OpRulesT)                 -> eq
  (PrecT, PrecT)                       -> eq
  -- | T0
  (BindT, BindT)                       -> eq
  (DataConT, DataConT)                 -> eq
  (DeclT, DeclT)                       -> eq
  (DeclRecT, DeclRecT)                 -> eq
  (DeclTermT, DeclTermT)               -> eq
  (DeclTypeT, DeclTypeT)               -> eq
  (ExpT, ExpT)                         -> eq
  (PatT, PatT)                         -> eq
  (ProgramT, ProgramT)                 -> eq
  (StmtT, StmtT)                       -> eq
  (TokT, TokT)                         -> eq
  -- | T1
  (QTypeT, QTypeT)                     -> eq
  (TypeConstraintT, TypeConstraintT)   -> eq
  (TypeT, TypeT)                       -> eq
  (TypePatT, TypePatT)                 -> eq
  -- | T2
  (KindT, KindT)                       -> eq
  (KindConstraintT, KindConstraintT)   -> eq
  -- | Solver
  (TypeRequirementT, TypeRequirementT) -> eq
  (KindRequirementT, KindRequirementT) -> eq
  -- |
  _                                    -> neq


sub :: forall a s. (IsTerm a, IsStage s) => (forall b. IsTerm b => Annotated s b -> Maybe (Annotated s b)) -> Annotated s a -> Annotated s a
sub f x = case f x of
  Just y  -> y
  Nothing -> runIdentity $ recurse (Identity . sub f) x

extract :: forall m a s. (Monoid m, IsTerm a, IsStage s) => (forall b. IsTerm b => b s -> m) -> Annotated s a -> m
extract f (_ :< x) = f x <> (getConst $ recurseTerm (Const . extract f) x)

deepExtract :: forall m a s. (Monoid m, IsTerm a, IsStage s) => (forall b. IsTerm b => b s -> m) -> Annotated s a -> m
deepExtract f x = f (view value x) <> (getConst $ recurse (Const . deepExtract f :: TermAction (Const m) s s) x)

embedSub :: forall a s. (IsTerm a, IsStage s) => (Annotated s a -> Maybe (Annotated s a)) -> (forall b. IsTerm b => Annotated s b -> Maybe (Annotated s b))
embedSub f x = transferM f x where
  transferM :: forall f a b s. (IsTerm a, IsTerm b, IsStage s) => (Annotated s a -> Maybe (Annotated s a)) -> Annotated s b -> Maybe (Annotated s b)
  transferM f x = switch (witness :: TermT a) (witness :: TermT b) (f x) Nothing

embedMonoid :: forall a b s. (Monoid b, IsTerm a, IsStage s) => (a s -> b) -> (forall a. IsTerm a => a s -> b)
embedMonoid f x = getConst $ transferA (Const . f) x where
  transferA :: forall f a b s. (Applicative f, IsTerm a, IsTerm b, IsStage s) => (a s -> f (a s)) -> b s -> f (b s)
  transferA f x = switch (witness :: TermT a) (witness :: TermT b) (f x) (pure x)


-- Implementations below here

-- TODO use template haskell to generate recurseTerm

 -- TODO need to assert void!
trivial :: (Applicative f, IsTerm a, IsStage s, Annotation s a ~ Void) => TermT a -> TermAction f s t -> Annotation s a -> f (Annotation t a)
trivial _ _ = absurd

-- | Operators

instance IsTerm Op where
  witness = OpT
  recurseAnnotation _ = trivial
  recurseTerm _ = \case
    Op ns -> pure (Op ns)

instance IsTerm OpRules where
  witness = OpRulesT
  recurseAnnotation _ = trivial
  recurseTerm f = \case
    OpRules rs -> OpRules <$> traverse (\case { Left assoc -> Left <$> pure assoc; Right precs -> Right <$> traverse f precs }) rs

instance IsTerm Prec where
  witness = PrecT
  recurseAnnotation _ = trivial
  recurseTerm f = \case
    Prec ord op -> Prec ord <$> f op

-- | T0

instance IsTerm Bind where
  witness = BindT
  recurseAnnotation _ = trivial
  recurseTerm f = \case
    Bind a b -> Bind <$> f a <*> f b

instance IsTerm DataCon where
  witness = DataConT
  recurseAnnotation s _ f = case s of
    InitialT   -> absurd
    ParseT     -> absurd
    KindCheckT -> absurd
    TypeCheckT -> f
  recurseTerm f = \case
    DataCon n t -> DataCon n <$> f t

instance IsTerm Decl where
  witness = DeclT
  recurseAnnotation _ = trivial
  recurseTerm f = \case
    DeclOpSugar o d rs -> DeclOpSugar <$> f o <*> pure d <*> f rs
    DeclRec ds         -> DeclRec <$> traverse f ds
    DeclSynSugar n t   -> DeclSynSugar n <$> f t
    DeclTerm d         -> DeclTerm <$> f d
    DeclType d         -> DeclType <$> f d

instance IsTerm DeclRec where
  witness = DeclRecT
  recurseAnnotation _ = trivial
  recurseTerm f = \case
    DeclRecType d         -> DeclRecType <$> f d
    DeclRecTerm d         -> DeclRecTerm <$> f d

instance IsTerm DeclTerm where
  witness = DeclTermT
  recurseAnnotation _ = trivial
  recurseTerm f = \case
    DeclTermVar n t e       -> DeclTermVar n <$> traverse f t <*> f e
    DeclTermDefSugar n ps e -> DeclTermDefSugar n <$> traverse f ps <*> f e
    DeclTermSigSugar n t    -> DeclTermSigSugar n <$> f t

instance IsTerm DeclType where
  witness = DeclTypeT
  recurseAnnotation s _ f = case s of
    InitialT   -> absurd
    ParseT     -> absurd
    KindCheckT -> f
    TypeCheckT -> absurd
  recurseTerm f = \case
    DeclTypeData m n t as      -> DeclTypeData m n <$> traverse f t <*> traverse f as
    DeclTypeDataSugar m n t as -> DeclTypeDataSugar m n <$> traverse f t <*> traverse f as
    DeclTypeEnum n as          -> pure (DeclTypeEnum n as)


pair :: (IsTerm a, IsTerm b) => Applicative f => TermAction f s t -> (Annotated s a, Annotated s b) -> f (Annotated t a, Annotated t b)
pair f (a, b) = (,) <$> f a <*> f b

pairs :: (IsTerm a, IsTerm b) => Applicative f => TermAction f s t -> [(Annotated s a, Annotated s b)] -> f [(Annotated t a, Annotated t b)]
pairs f = traverse (pair f)

instance IsTerm Exp where
  witness = ExpT
  recurseAnnotation s _ f = case s of
    InitialT   -> absurd
    ParseT     -> absurd
    KindCheckT -> absurd
    TypeCheckT -> f
  recurseTerm f = \case
    Apply a b       -> Apply <$> f a <*> f b
    Case a as       -> Case <$> f a <*> pairs f as
    Cases as        -> Cases <$> pairs f as
    Capture cs e    -> Capture <$> traverse (second f) cs <*> f e
    Con n           -> pure (Con n)
    Defer a b       -> Defer <$> f a <*> f b
    DoSugar ss      -> DoSugar <$> traverse f ss
    If a b c        -> If <$> f a <*> f b <*> f c
    Lambda a b      -> Lambda <$> f a <*> f b
    Let a b         -> Let <$> f a <*> f b
    Lit l           -> pure (Lit l)
    MixfixSugar ts  -> MixfixSugar <$> traverse f ts
    Read n a        -> Read n <$> f a
    Pair a b        -> Pair <$> f a <*> f b
    Seq a b         -> Seq <$> f a <*> f b
    Sig e t         -> Sig <$> f e <*> f t
    Specialize e xs -> Specialize <$> f e <*> pairs f xs
    Switch as       -> Switch <$> pairs f as
    Unit            -> pure Unit
    Var n           -> pure (Var n)
    VarRefSugar n   -> pure (VarRefSugar n)
    Where a bs      -> Where <$> f a <*> traverse f bs

instance IsTerm Pat where
  witness = PatT
  recurseAnnotation s _ f = case s of
    InitialT   -> absurd
    ParseT     -> absurd
    KindCheckT -> absurd
    TypeCheckT -> f
  recurseTerm f = \case
    PatAt n a   -> PatAt n <$> f a
    PatData n p -> PatData n <$> f p
    PatEnum n   -> pure (PatEnum n)
    PatHole     -> pure PatHole
    PatLit l    -> pure (PatLit l)
    PatPair a b -> PatPair <$> f a <*> f b
    PatUnit     -> pure PatUnit
    PatVar n    -> pure (PatVar n)

instance IsTerm Program where
  witness = ProgramT
  recurseAnnotation _ = trivial
  recurseTerm f = \case
    Program ds -> Program <$> traverse f ds

instance IsTerm Stmt where
  witness = StmtT
  recurseAnnotation _ = trivial
  recurseTerm f = \case
    StmtBind b -> StmtBind <$> f b
    StmtExp e  -> StmtExp <$> f e

instance IsTerm Tok where
  witness = TokT
  recurseAnnotation _ = trivial
  recurseTerm f = \case
    TokExp e -> TokExp <$> f e
    TokOp o  -> pure (TokOp o)

-- | T1

instance IsTerm QType where
  witness = QTypeT
  recurseAnnotation _ = trivial
  recurseTerm f = \case
    Forall vs cs t -> Forall <$> traverse f vs <*> traverse f cs <*> f t
    Mono t         -> Mono <$> f t

instance IsTerm TypeConstraint where
  witness = TypeConstraintT
  recurseAnnotation _ = trivial
  recurseTerm f = \case
    TypeIsEq a b            -> TypeIsEq <$> f a <*> f b
    TypeIsEqIfAffine a b t  -> TypeIsEqIfAffine <$> f a <*> f b <*> f t
    TypeIsInstance t        -> TypeIsInstance <$> f t
    TypeIsIntegralOver t n  -> TypeIsIntegralOver <$> f t <*> pure n
    TypeIsRef t             -> TypeIsRef <$> f t
    TypeIsRefFree t n       -> TypeIsRefFree <$> f t <*> pure n
    TypeIsSub a b           -> TypeIsSub <$> f a <*> f b
    TypeIsSubIfAffine a b t -> TypeIsSubIfAffine <$> f a <*> f b <*> f t
    TypeIsValue t           -> TypeIsValue <$> f t

instance IsTerm Type where
  witness = TypeT
  recurseAnnotation s _ f = case s of
    InitialT   -> absurd
    ParseT     -> absurd
    KindCheckT -> f
    TypeCheckT -> absurd
  recurseTerm f = \case
    TypeApply a b   -> TypeApply <$> f a <*> f b
    TypeApplyOp a b -> TypeApplyOp <$> f a <*> f b
    TypeCon n       -> pure (TypeCon n)
    TypeFn a b      -> TypeFn <$> f a <*> f b
    TypeIdentityOp  -> pure TypeIdentityOp
    TypePair a b    -> TypePair <$> f a <*> f b
    TypeRef n       -> pure (TypeRef n)
    TypeSetOp os    -> TypeSetOp . Set.fromList <$> traverse f (Set.toList os)
    TypeUni f n     -> pure (TypeUni f n)
    TypeUnit        -> pure TypeUnit
    TypeVar f n     -> pure (TypeVar f n)

instance IsTerm TypePat where
  witness = TypePatT
  recurseAnnotation s _ f = case s of
    InitialT   -> absurd
    ParseT     -> absurd
    KindCheckT -> f
    TypeCheckT -> absurd
  recurseTerm _ = \case
    TypePatVar f n -> pure (TypePatVar f n)

-- | T2

instance IsTerm Kind where
  witness = KindT
  recurseAnnotation _ = trivial
  recurseTerm f = \case
    KindConstraint -> pure KindConstraint
    KindFn a b     -> KindFn <$> f a <*> f b
    KindRef        -> pure KindRef
    KindType       -> pure KindType
    KindUni n      -> pure (KindUni n)
    KindView       -> pure KindView

instance IsTerm KindConstraint where
  witness = KindConstraintT
  recurseAnnotation _ = trivial
  recurseTerm f = \case
    KindIsEq k l  -> KindIsEq <$> f k <*> f l
    KindIsPlain k -> KindIsPlain <$> f k
    KindIsSub k l -> KindIsSub <$> f k <*> f l

-- | Solver

instance IsTerm (Requirement TypeConstraint) where
  witness = TypeRequirementT
  recurseAnnotation s _ f = case s of
    InitialT   -> absurd
    ParseT     -> absurd
    KindCheckT -> absurd
    TypeCheckT -> \case
      TypeReasonApply a b              -> TypeReasonApply <$> f a <*> f b
      TypeReasonBind p e               -> TypeReasonBind <$> f p <*> f e
      TypeReasonCaptured n             -> pure (TypeReasonCaptured n)
      TypeReasonCaseCongruence         -> pure TypeReasonCaseCongruence
      TypeReasonConstructor n          -> pure (TypeReasonConstructor n)
      TypeReasonFunctionCongruence n s -> TypeReasonFunctionCongruence n <$> traverse f s
      TypeReasonIfCondition            -> pure TypeReasonIfCondition
      TypeReasonIfCongruence           -> pure TypeReasonIfCongruence
      TypeReasonIntegerLiteral i       -> pure (TypeReasonIntegerLiteral i)
      TypeReasonMultiAlias n           -> pure (TypeReasonMultiAlias n)
      TypeReasonMultiUse n             -> pure (TypeReasonMultiUse n)
      TypeReasonRead n                 -> pure (TypeReasonRead n)
      TypeReasonSignature t            -> TypeReasonSignature <$> f t
      TypeReasonSpecialization n       -> pure (TypeReasonSpecialization n)
      TypeReasonSwitchCondition        -> pure TypeReasonSwitchCondition
      TypeReasonSwitchCongruence       -> pure TypeReasonSwitchCongruence
  recurseTerm f = \case
    Requirement c -> Requirement <$> recurseTerm f c

instance IsTerm (Requirement KindConstraint) where
  witness = KindRequirementT
  recurseAnnotation s _ f = case s of
    InitialT   -> absurd
    ParseT     -> absurd
    KindCheckT -> \case
      KindReasonData n a        -> KindReasonData n <$> traverse f a
      KindReasonDataCon c       -> KindReasonDataCon <$> f c
      KindReasonQType t         -> KindReasonQType <$> f t
      KindReasonTypeApply a b   -> KindReasonTypeApply <$> f a <*> f b
      KindReasonTypeApplyOp a b -> KindReasonTypeApplyOp <$> f a <*> f b
      KindReasonType t          -> KindReasonType <$> f t
      KindReasonTypePat t       -> KindReasonTypePat <$> f t
    TypeCheckT -> absurd
  recurseTerm f = \case
    Requirement c -> Requirement <$> recurseTerm f c
