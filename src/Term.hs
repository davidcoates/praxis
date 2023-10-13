{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE OverloadedStrings    #-}
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
  , Decl(..)
  , Exp(..)
  , Lit(..)
  , Pat(..)
  , Program(..)
  , Stmt(..)
  , Tok(..)

  -- | T1
  , TyOpDomain(..)
  , TyOp(..)
  , TyPat(..)
  , Type(..)
  , QTyVar(..)
  , QType(..)

  -- | T2
  , Kind(..)

  -- | Solver
  , KindConstraint(..)
  , TyConstraint(..)
  , Prop(..)
  , TyProp
  , KindProp

  , Annotation
  , Annotated
  , source
  , annotation
  , split
  , splitPair
  , splitTrivial
  , phantom
  , as
  , covalue

  , Derivation(..)
  , DataConInfo(..)
  ) where

import           Common

import           Data.Set (Set)

-- * OPERATORS *

data Assoc = AssocLeft | AssocRight
  deriving (Eq, Ord)

data Op = Op [Maybe Name] -- TDO qualification over this
  deriving (Eq, Ord)

data OpRules = OpRules (Maybe (Annotated Assoc)) [Annotated Prec]
             | OpMultiRules [Either (Annotated Assoc) [Annotated Prec]] -- ^Parsing only
  deriving (Eq, Ord)

data Prec = Prec Ordering Op
  deriving (Eq, Ord)


-- * DECLARATIONS & EXPRESSIONS *

data Bind = Bind (Annotated Pat) (Annotated Exp)
  deriving (Eq, Ord)

data DataCon = DataCon Name (Maybe (Annotated Type))
  deriving (Eq, Ord)

data Decl = DeclData Name (Maybe (Annotated TyPat)) [Annotated DataCon]
          | DeclFun Name [Annotated Pat] (Annotated Exp) -- ^ Parsing only
          | DeclOp (Annotated Op) Name (Annotated OpRules) -- FIXME Qualified Name
          | DeclSig Name (Annotated QType) -- ^ Parsing only
          | DeclSyn Name (Annotated Type) -- ^ Parsing only
          | DeclVar Name (Maybe (Annotated QType)) (Annotated Exp)
  deriving (Eq, Ord)

data Exp = Apply (Annotated Exp) (Annotated Exp)
         | Case (Annotated Exp) [(Annotated Pat, Annotated Exp)]
         | Cases [(Annotated Pat, Annotated Exp)]
         | Con Name
         | Do [Annotated Stmt]
         | If (Annotated Exp) (Annotated Exp) (Annotated Exp)
         | Lambda (Annotated Pat) (Annotated Exp)
         | Let (Annotated Bind) (Annotated Exp)
         | Lit Lit
         | Mixfix [Annotated Tok] -- ^ Parsing only
         | Read Name (Annotated Exp)
         | Pair (Annotated Exp) (Annotated Exp)
         | Sig (Annotated Exp) (Annotated Type)
         | Switch [(Annotated Exp, Annotated Exp)]
         | Unit
         | Var Name -- FIXME Qualified Name
         | VarRef Name -- ^ Parsing only
         | Where (Annotated Exp) [Annotated Decl]
  deriving (Eq, Ord)

data Lit = Bool Bool
         | Char Char
         | Int Int
         | String String
  deriving (Eq, Ord)

-- TODO remove?
instance Show Lit where
  show = \case
    Bool b   -> show b
    Char c   -> show c
    Int i    -> show i
    String s -> show s

data Pat = PatAt Name (Annotated Pat)
         | PatCon Name (Maybe (Annotated Pat))
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

-- |Parsing only
data Tok = TExp (Annotated Exp)
         | TOp Name
  deriving (Eq, Ord)

data TyOpDomain = Ref | RefOrId
  deriving (Eq, Ord)

data TyOp = TyOpUni TyOpDomain Name
          | TyOpId
          | TyOpRef Name
          | TyOpVar TyOpDomain Name
  deriving (Eq, Ord)

data TyPat = TyPatPack (Annotated TyPat) (Annotated TyPat)
           | TyPatVar Name
           | TyPatOpVar TyOpDomain Name
  deriving (Eq, Ord)

data Type = TyUni Name -- Compares less than all other types
          | TyApply (Annotated Type) (Annotated Type)
          | TyCon Name
          | TyFun (Annotated Type) (Annotated Type)
          | TyOp (Annotated TyOp)
          | TyPack (Annotated Type) (Annotated Type)
          | TyPair (Annotated Type) (Annotated Type)
          | TyUnit
          | TyVar Name
  deriving (Eq, Ord)

data QTyVar = QTyVar Name | QTyOpVar TyOpDomain Name
  deriving (Eq, Ord)

data QType = Forall [Annotated QTyVar] [Annotated TyConstraint] (Annotated Type)
  deriving (Eq, Ord)

data Kind = KindUni Name
          | KindConstraint
          | KindFun (Annotated Kind) (Annotated Kind)
          | KindOp
          | KindPair (Annotated Kind) (Annotated Kind)
          | KindType
  deriving (Eq, Ord)

data TyConstraint = Class (Annotated Type)
                  | Share (Annotated Type)
                  | TEq (Annotated Type) (Annotated Type)
                  | TOpEq (Annotated Type) (Annotated Type)
                  | RefFree Name (Annotated Type)
  deriving (Eq, Ord)

infixl 8 `TEq`
infixl 8 `TOpEq`

data KindConstraint = KEq (Annotated Kind) (Annotated Kind)
  deriving (Eq, Ord)

data Prop a = Top
            | Bottom
            | Exactly a
            | And (Prop a) (Prop a)
  deriving (Eq, Ord)

type TyProp = Prop TyConstraint

type KindProp = Prop KindConstraint

type family Annotation a where
  Annotation Exp      = Annotated Type
  Annotation Pat      = Annotated Type
  Annotation TyPat    = Annotated Kind
  Annotation Type     = Annotated Kind
  Annotation DataCon  = DataConInfo
  Annotation TyProp   = Derivation TyProp
  Annotation KindProp = Derivation KindProp
  Annotation a        = Void

type Annotated a = Tag (Source, Maybe (Annotation a)) a

source :: Functor f => (Source -> f Source) -> Annotated a -> f (Annotated a)
source = tag . first

annotation :: Functor f => (Maybe (Annotation a) -> f (Maybe (Annotation a))) -> Annotated a -> f (Annotated a)
annotation = tag . second

split :: Functor f => (Source -> a -> f (Tag (Annotation a) a)) -> Annotated a -> f (Annotated a)
split f ((s, _) :< x) = (\(a :< x) -> ((s, Just a)) :< x) <$> f s x

splitPair :: Functor f => (Source -> a -> f (b, Tag (Annotation a) a)) -> Annotated a -> f (b, Annotated a)
splitPair f = runPairT . split (\s a -> PairT (f s a))

splitTrivial :: Functor f => (Source -> a -> f a) -> Annotated a -> f (Annotated a)
splitTrivial f ((s, _) :< x) = (\x -> ((s, Nothing) :< x)) <$> f s x

phantom :: a -> Annotated a
phantom x = (Phantom, Nothing) :< x

as :: a -> Annotation a -> Annotated a
as x a = (Phantom, Just a) :< x

covalue :: Functor f => (Annotated a -> f (Annotated a)) -> a -> f a
covalue f x = view value <$> f (phantom x)

-- TODO should this be somewhere else?
data Derivation a = Root String
                  | Antecedent (Annotated a)

instance Pretty (Annotated a) => Pretty (Derivation a) where
  pretty (Root r)       = "\n|-> (" <> pretty r <> ")"
  pretty (Antecedent a) = "\n|-> " <> pretty a

{- | A data constructor C for a type T, either has:

C : forall vs. A -> T vs
or
C : forall vs. T vs

Here "A" is the argType, "T vs" is the retType.
-}
data DataConInfo = DataConInfo { fullType :: Annotated QType, argType :: Maybe (Annotated Type), retType :: Annotated Type }

instance (Pretty (Annotated Type), Pretty (Annotated QType)) => Pretty DataConInfo where
  pretty (DataConInfo { fullType }) = pretty fullType
