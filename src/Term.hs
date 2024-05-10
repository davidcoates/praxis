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
  , ViewDomain(..)
  , View(..)
  , TyPat(..)
  , Type(..)
  , TyConstraint(..)
  , QTyVar(..)
  , QType(..)

  -- | T2
  , Kind(..)
  , KindConstraint(..)

  -- | Solver
  , Requirement(..)
  , TyRequirement(..)
  , KindRequirement(..)
  , TyReason(..)
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

data DeclType = DeclTypeData DataMode Name (Maybe (Annotated TyPat)) [Annotated DataCon]
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
type Specialisation = [(Annotated QTyVar, Annotated Type)]

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

data Tok = TExp (Annotated Exp)
         | TOp Name
  deriving (Eq, Ord)

data ViewDomain = Ref | RefOrValue -- Note: The order here matters for the solvers
  deriving (Eq, Ord)

data View = ViewUni ViewDomain Name
          | ViewValue
          | ViewRef Name
          | ViewVar ViewDomain Name
  deriving (Eq, Ord)

data TyPat = TyPatPack (Annotated TyPat) (Annotated TyPat)
           | TyPatVar Name
           | TyPatViewVar ViewDomain Name
  deriving (Eq, Ord)

data Type = TyUni Name -- Compares less than all other types
          | TyApply (Annotated Type) (Annotated Type)
          | TyCon Name
          | TyFn (Annotated Type) (Annotated Type)
          | TyView (Annotated View)
          | TyPack (Annotated Type) (Annotated Type)
          | TyPair (Annotated Type) (Annotated Type)
          | TyUnit
          | TyVar Name
  deriving (Eq, Ord)

data QTyVar = QTyVar Name | QViewVar ViewDomain Name
  deriving (Eq, Ord)

data QType = Forall [Annotated QTyVar] [Annotated TyConstraint] (Annotated Type)
  deriving (Eq, Ord)

data Kind = KindUni Name
          | KindConstraint
          | KindFn (Annotated Kind) (Annotated Kind)
          | KindView ViewDomain
          | KindPair (Annotated Kind) (Annotated Kind)
          | KindType
  deriving (Eq, Ord)

data TyConstraint = HoldsInteger Integer (Annotated Type)
                  | Instance (Annotated Type)
                  | RefFree Name (Annotated Type)
                  | TEq (Annotated Type) (Annotated Type)
                  | TOpEq (Annotated Type) (Annotated Type)
  deriving (Eq, Ord)

infixl 8 `TEq`
infixl 8 `TOpEq`

data KindConstraint = KEq (Annotated Kind) (Annotated Kind)
                    | KSub (Annotated Kind) (Annotated Kind)
  deriving (Eq, Ord)

infixl 8 `KEq`
infixl 8 `KSub`

newtype Requirement a = Requirement a
  deriving (Eq, Ord)

type TyRequirement = Requirement TyConstraint
type KindRequirement = Requirement KindConstraint

type family Annotation a where
  Annotation Exp      = Annotated Type
  Annotation Pat      = Annotated Type
  Annotation TyPat    = Annotated Kind
  Annotation Type     = Annotated Kind
  Annotation QTyVar   = Annotated Kind
  Annotation View     = Annotated Kind
  Annotation DataCon  = Annotated QType
  Annotation DeclType = Annotated Kind
  Annotation TyRequirement   = TyReason
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

data TyReason = TyReasonApply (Annotated Exp) (Annotated Exp)
              | TyReasonBind (Annotated Pat) (Annotated Exp)
              | TyReasonRead Name
              | TyReasonIntegerLiteral Integer
              -- TODO
              | Captured Name
              | CaseCongruence
              | ConPattern Name
              | FnCongruence Name
              | FnSignature Name
              | IfCondition
              | IfCongruence
              | InstanceOf Name
              | MultiAlias Name
              | MultiUse Name
              | Specialisation Name
              | SwitchCondition
              | SwitchCongruence
              | UserSignature
  deriving (Eq, Ord)

data KindReason = KindReasonTyApply (Annotated Type) (Annotated Type)
                | KindReasonDataCon (Annotated DataCon)
                | KindReasonData Name (Maybe (Annotated TyPat))
                | KindReasonType (Annotated Type)
  deriving (Eq, Ord)

