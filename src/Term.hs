{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE Strict               #-}
{-# LANGUAGE StrictData           #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

module Term
  -- | Operators
  ( Assoc(..)
  , Op(..)
  , OpRules(..)
  , Prec(..)

  -- | T0
  , Bind(..)
  , DataCon(..)
  , DataMode(..)
  , Decl(..)
  , DeclTerm(..)
  , DeclType(..)
  , Exp(..)
  , Lit(..)
  , Pat(..)
  , Program(..)
  , Specialisation
  , Stmt(..)
  , Tok(..)

  -- | T1
  , Flavor(..)
  , QType(..)
  , TypeConstraint(..)
  , Type(..)
  , TypePat(..)

  -- | T2
  , Kind(..)
  , KindConstraint(..)

  -- | Solver
  , Requirement(..)
  , TypeRequirement(..)
  , KindRequirement(..)
  , TypeReason(..)
  , KindReason(..)

  , Annotation
  , Annotated
  , source
  , annotation
  , phantom
  , as
  ) where

import           Common

import           Data.Set (Set)

-- * OPERATORS *

data Assoc = AssocLeft | AssocRight
  deriving (Eq, Ord)

data Op = Op [Maybe Name] -- TDO qualification over this
  deriving (Eq, Ord)

data OpRules = OpRules (Maybe (Annotated Assoc)) [Annotated Prec]
             | OpRulesSweet [Either (Annotated Assoc) [Annotated Prec]]
  deriving (Eq, Ord)

data Prec = Prec Ordering Op
  deriving (Eq, Ord)


-- * DECLARATIONS & EXPRESSIONS *

data Bind = Bind (Annotated Pat) (Annotated Exp)
  deriving (Eq, Ord)

data DataCon = DataCon Name (Annotated Type)
  deriving (Eq, Ord)

data DataMode = DataUnboxed | DataBoxed | DataRec
  deriving (Eq, Ord)

data DeclType = DeclTypeData DataMode Name [Annotated TypePat] [Annotated DataCon]
              | DeclTypeEnum Name [Name]
  deriving  (Eq, Ord)

data DeclTerm = DeclTermRec [Annotated DeclTerm]
              | DeclTermVar Name (Maybe (Annotated QType)) (Annotated Exp)
              | DeclTermDefSweet Name [Annotated Pat] (Annotated Exp)
              | DeclTermSigSweet Name (Annotated QType)
  deriving (Eq, Ord)

data Decl = DeclOpSweet (Annotated Op) Name (Annotated OpRules)
          | DeclSynSweet Name (Annotated Type)
          | DeclType (Annotated DeclType)
          | DeclTerm (Annotated DeclTerm)
  deriving (Eq, Ord)

-- TODO constraints
type Specialisation = [(Annotated TypePat, Annotated Type)]

data Exp = Apply (Annotated Exp) (Annotated Exp)
         | Case (Annotated Exp) [(Annotated Pat, Annotated Exp)]
         | Cases [(Annotated Pat, Annotated Exp)]
         | Closure [(Name, Annotated QType)] (Annotated Exp)
         | Con Name
         | Defer (Annotated Exp) (Annotated Exp)
         | DoSweet [Annotated Stmt]
         | If (Annotated Exp) (Annotated Exp) (Annotated Exp)
         | Lambda (Annotated Pat) (Annotated Exp)
         | Let (Annotated Bind) (Annotated Exp)
         | Lit Lit
         | MixfixSweet [Annotated Tok]
         | Read Name (Annotated Exp)
         | Pair (Annotated Exp) (Annotated Exp)
         | Seq (Annotated Exp) (Annotated Exp)
         | Sig (Annotated Exp) (Annotated Type)
         | Specialise (Annotated Exp) Specialisation
         | Switch [(Annotated Exp, Annotated Exp)]
         | Unit
         | Var Name
         | VarRefSweet Name
         | Where (Annotated Exp) [Annotated DeclTerm]
  deriving (Eq, Ord)

-- TODO: Array literals?
data Lit = Bool Bool
         | Char Char
         | Integer Integer
         | String String
  deriving (Eq, Ord)

-- TODO remove?
instance Show Lit where
  show = \case
    Bool b    -> show b
    Char c    -> show c
    Integer i -> show i
    String s  -> show s

data Pat = PatAt Name (Annotated Pat)
         | PatData Name (Annotated Pat)
         | PatEnum Name
         | PatHole
         | PatLit Lit
         | PatPair (Annotated Pat) (Annotated Pat)
         | PatUnit
         | PatVar Name
  deriving (Eq, Ord)

data Program = Program [Annotated Decl]
  deriving (Eq, Ord)

data Stmt = StmtBind (Annotated Bind)
          | StmtExp (Annotated Exp)
  deriving (Eq, Ord)

data Tok = TokExp (Annotated Exp)
         | TokOp Name
  deriving (Eq, Ord)

data Flavor = Plain | Ref | Value | View
  deriving (Eq, Ord)

data TypePat = TypePatVar Flavor Name
  deriving (Eq, Ord)

data Type = TypeApply (Annotated Type) (Annotated Type)
          | TypeApplyOp (Annotated Type) (Annotated Type)
          | TypeCon Name
          | TypeFn (Annotated Type) (Annotated Type)
          | TypeIdentityOp
          | TypePair (Annotated Type) (Annotated Type)
          | TypeRef Name
          | TypeSetOp (Set (Annotated Type))
          | TypeUni Flavor Name
          | TypeUnit
          | TypeVar Flavor Name
  deriving (Eq, Ord)

data QType = Forall [Annotated TypePat] [Annotated TypeConstraint] (Annotated Type)
           | Mono (Annotated Type)
  deriving (Eq, Ord)

data Kind = KindUni Name
          | KindConstraint
          | KindFn (Annotated Kind) (Annotated Kind)
          | KindRef
          | KindType
          | KindView
  deriving (Eq, Ord)

data TypeConstraint = TypeIsEq (Annotated Type) (Annotated Type)
                    | TypeIsEqIfAffine (Annotated Type) (Annotated Type) (Annotated Type)
                    | TypeIsInstance (Annotated Type)
                    | TypeIsIntegralOver (Annotated Type) Integer
                    | TypeIsRef (Annotated Type)
                    | TypeIsRefFree (Annotated Type) Name
                    | TypeIsSub (Annotated Type) (Annotated Type)
                    | TypeIsSubIfAffine (Annotated Type) (Annotated Type) (Annotated Type)
                    | TypeIsValue (Annotated Type)
  deriving (Eq, Ord)

infixl 8 `TypeIsEq`
infixl 8 `TypeIsSub`

data KindConstraint = KindIsEq (Annotated Kind) (Annotated Kind)
                    | KindIsPlain (Annotated Kind)
                    | KindIsSub (Annotated Kind) (Annotated Kind)
  deriving (Eq, Ord)

infixl 8 `KindIsEq`
infixl 8 `KindIsSub`

newtype Requirement a = Requirement a
  deriving (Eq, Ord)

type TypeRequirement = Requirement TypeConstraint
type KindRequirement = Requirement KindConstraint

type family Annotation a where
  Annotation Exp      = Annotated Type
  Annotation Pat      = Annotated Type
  Annotation Type     = Annotated Kind
  Annotation TypePat  = Annotated Kind
  Annotation DataCon  = Annotated QType
  Annotation DeclType = Annotated Kind
  Annotation TypeRequirement = TypeReason
  Annotation KindRequirement = KindReason
  Annotation a               = Void

type Annotated a = Tag (Source, Maybe (Annotation a)) a

source :: Functor f => (Source -> f Source) -> Annotated a -> f (Annotated a)
source = tag . first

annotation :: Functor f => (Maybe (Annotation a) -> f (Maybe (Annotation a))) -> Annotated a -> f (Annotated a)
annotation = tag . second

phantom :: a -> Annotated a
phantom x = (Phantom, Nothing) :< x

as :: a -> Annotation a -> Annotated a
as x a = (Phantom, Just a) :< x

data TypeReason = TypeReasonApply (Annotated Exp) (Annotated Exp)
                | TypeReasonBind (Annotated Pat) (Annotated Exp)
                | TypeReasonCaptured Name
                | TypeReasonCaseCongruence
                | TypeReasonConstructor Name
                | TypeReasonFunctionCongruence Name (Maybe (Annotated QType))
                | TypeReasonRead Name
                | TypeReasonIfCondition
                | TypeReasonIfCongruence
                | TypeReasonIntegerLiteral Integer
                | TypeReasonMultiAlias Name
                | TypeReasonMultiUse Name
                | TypeReasonSignature (Annotated Type)
                | TypeReasonSpecialisation Name
                | TypeReasonSwitchCondition
                | TypeReasonSwitchCongruence
  deriving (Eq, Ord)

data KindReason = KindReasonData Name [Annotated TypePat]
                | KindReasonDataCon (Annotated DataCon)
                | KindReasonQType (Annotated QType)
                | KindReasonTypeApply (Annotated Type) (Annotated Type)
                | KindReasonTypeApplyOp (Annotated Type) (Annotated Type)
                | KindReasonType (Annotated Type)
                | KindReasonTypePat (Annotated TypePat)
  deriving (Eq, Ord)

