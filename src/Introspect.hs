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
  IDeclRec  :: I DeclRec
  IDeclTerm :: I DeclTerm
  IDeclType :: I DeclType
  IExp      :: I Exp
  IPat      :: I Pat
  IProgram  :: I Program
  IStmt     :: I Stmt
  ITok      :: I Tok
  -- | T1
  IQType          :: I QType
  ITypeConstraint :: I TypeConstraint
  IType           :: I Type
  ITypePat        :: I TypePat
  -- | T2
  IKind           :: I Kind
  IKindConstraint :: I KindConstraint
  -- | Solver
  ITypeRequirement :: I TypeRequirement
  IKindRequirement :: I KindRequirement

deriving instance Show (I a)

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
  (IDeclRec, IDeclRec)                 -> eq
  (IDeclTerm, IDeclTerm)               -> eq
  (IDeclType, IDeclType)               -> eq
  (IExp, IExp)                         -> eq
  (IPat, IPat)                         -> eq
  (IProgram, IProgram)                 -> eq
  (IStmt, IStmt)                       -> eq
  (ITok, ITok)                         -> eq
  -- | T1
  (IQType, IQType)                     -> eq
  (ITypeConstraint, ITypeConstraint)   -> eq
  (IType, IType)                       -> eq
  (ITypePat, ITypePat)                 -> eq
  -- | T2
  (IKind, IKind)                       -> eq
  (IKindConstraint, IKindConstraint)   -> eq
  -- | Solver
  (ITypeRequirement, ITypeRequirement) -> eq
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
    OpRules rs -> OpRules <$> traverse (bitraverse f (traverse f)) rs

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
    DeclOpSugar o d rs -> DeclOpSugar <$> f o <*> pure d <*> f rs
    DeclRec ds         -> DeclRec <$> traverse f ds
    DeclSynSugar n t   -> DeclSynSugar n <$> f t
    DeclTerm d         -> DeclTerm <$> f d
    DeclType d         -> DeclType <$> f d

instance Term DeclRec where
  witness = IDeclRec
  recurseAnnotation = trivial
  recurseTerm f = \case
    DeclRecType d         -> DeclRecType <$> f d
    DeclRecTerm d         -> DeclRecTerm <$> f d

instance Term DeclTerm where
  witness = IDeclTerm
  recurseAnnotation = trivial
  recurseTerm f = \case
    DeclTermVar n t e       -> DeclTermVar n <$> traverse f t <*> f e
    DeclTermDefSugar n ps e -> DeclTermDefSugar n <$> traverse f ps <*> f e
    DeclTermSigSugar n t    -> DeclTermSigSugar n <$> f t

instance Term DeclType where
  witness = IDeclType
  recurseAnnotation _ f x = f x
  recurseTerm f = \case
    DeclTypeData m n t as      -> DeclTypeData m n <$> traverse f t <*> traverse f as
    DeclTypeDataSugar m n t as -> DeclTypeDataSugar m n <$> traverse f t <*> traverse f as
    DeclTypeEnum n as          -> pure (DeclTypeEnum n as)


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

instance Term TypeConstraint where
  witness = ITypeConstraint
  recurseAnnotation = trivial
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

instance Term Type where
  witness = IType
  recurseAnnotation _ f x = f x
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

instance Term TypePat where
  witness = ITypePat
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
    KindIsEq k l  -> KindIsEq <$> f k <*> f l
    KindIsPlain k -> KindIsPlain <$> f k
    KindIsSub k l -> KindIsSub <$> f k <*> f l

-- | Solver

instance Term TypeRequirement where
  witness = ITypeRequirement
  recurseAnnotation _ f x = case x of
    TypeReasonApply a b -> TypeReasonApply <$> f a <*> f b
    TypeReasonBind p e -> TypeReasonBind <$> f p <*> f e
    TypeReasonFunctionCongruence n s -> TypeReasonFunctionCongruence n <$> traverse f s
    TypeReasonSignature t -> TypeReasonSignature <$> f t
    _ -> pure x
  recurseTerm f = \case
    Requirement c -> Requirement <$> recurseTerm f c

instance Term KindRequirement where
  witness = IKindRequirement
  recurseAnnotation _ f x = case x of
    KindReasonData n a        -> KindReasonData n <$> traverse f a
    KindReasonDataCon c       -> KindReasonDataCon <$> f c
    KindReasonQType t         -> KindReasonQType <$> f t
    KindReasonTypeApply a b   -> KindReasonTypeApply <$> f a <*> f b
    KindReasonTypeApplyOp a b -> KindReasonTypeApplyOp <$> f a <*> f b
    KindReasonType t          -> KindReasonType <$> f t
    KindReasonTypePat t       -> KindReasonTypePat <$> f t
  recurseTerm f = \case
    Requirement c -> Requirement <$> recurseTerm f c
