{-# LANGUAGE FlexibleContexts     #-}
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
  , DataAlt(..)
  , Decl(..)
  , Exp(..)
  , Lit(..)
  , Pat(..)
  , Program(..)
  , Stmt(..)
  , Tok(..)

  -- | T1
  , TyOp(..)
  , TyPat(..)
  , Type(..)
  , QTyVar(..)
  , QType(..)

  -- | T2
  , Kind(..)

  -- | Solver
  , KindConstraint(..)
  , TypeConstraint(..)

  , Annotation
  , Annotated
  , source
  , annotation
  , split
  , splitTrivial
  , splitPair
  , phantom
  , as

  , Derivation(..)
  , DataAltInfo(..)
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

-- * DECLARATIONS *
data Decl = DeclData Name [Annotated TyPat] [Annotated DataAlt]
          | DeclFun Name [Annotated Pat] (Annotated Exp) -- ^Parsing only
          | DeclOp (Annotated Op) Name (Annotated OpRules) -- FIXME Qualified Name
          | DeclSig Name (Annotated QType) -- ^Parsing only
          | DeclSyn Name (Annotated Type) -- ^Parsing only
          | DeclVar Name (Maybe (Annotated QType)) (Annotated Exp)
  deriving (Eq, Ord)

data DataAlt = DataAlt Name (Maybe (Annotated Type))
  deriving (Eq, Ord)

-- * EXPRESSIONS *
data Exp = Apply (Annotated Exp) (Annotated Exp)
         | Case (Annotated Exp) [(Annotated Pat, Annotated Exp)]
         | Cases [(Annotated Pat, Annotated Exp)]
         | Con Name
         | Do [Annotated Stmt]
         | If (Annotated Exp) (Annotated Exp) (Annotated Exp)
         | Lambda (Annotated Pat) (Annotated Exp)
         | Let (Annotated Pat, Annotated Exp) (Annotated Exp) -- ^Parsing only TODO not parsing only?
         | Lit Lit
         | Mixfix [Annotated Tok] -- ^Parsing only
         | Read Name (Annotated Exp)
         | Pair (Annotated Exp) (Annotated Exp)
         | Sig (Annotated Exp) (Annotated Type)
         | Unit
         | Var Name -- FIXME Qualified Name
         | VarBang Name -- ^Parsing only
         | Where (Annotated Exp) [(Annotated Pat, Annotated Exp)]
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

data Stmt = StmtDecl (Annotated Decl)
          | StmtExp (Annotated Exp)
  deriving (Eq, Ord)

-- |Parsing only
data Tok = TExp (Annotated Exp)
         | TOp Name
  deriving (Eq, Ord)

data TyOp = TyOpUni Name
          | TyOpBang
          | TyOpId
          | TyOpVar Name
  deriving (Eq, Ord)

-- TODO TyPatPack
data TyPat = TyPatVar Name
  deriving (Eq, Ord)

data Type = TyUni Name -- Compares less than all other types
          | TyApply (Annotated Type) (Annotated Type)
          | TyCon Name
          | TyFun (Annotated Type) (Annotated Type)
          | TyOp (Annotated TyOp) (Annotated Type)
          | TyPair (Annotated Type) (Annotated Type)
          | TyUnit
          | TyVar Name
  deriving (Eq, Ord)

data QTyVar = QTyVar Name | QTyOpVar Name
  deriving (Eq, Ord)

data QType = Forall [QTyVar] (Annotated Type)
  deriving (Eq, Ord)

data Kind = KindUni Name
          | KindConstraint
          | KindFun (Annotated Kind) (Annotated Kind)
          | KindType
  deriving (Eq, Ord)

data TypeConstraint = Class (Annotated Type)
                    | Affine (Annotated Type)
                    | Share (Annotated Type)
                    | TEq (Annotated Type) (Annotated Type)
                    | TOpEq Name Name
  deriving (Eq, Ord)

infixl 8 `TEq`
infixl 8 `TOpEq`

data KindConstraint = KEq (Annotated Kind) (Annotated Kind)
  deriving (Eq, Ord)

type family Annotation a where
  Annotation Exp            = Annotated Type
  Annotation Pat            = Annotated Type
  Annotation TyPat          = Annotated Kind
  Annotation Type           = Annotated Kind
  Annotation TypeConstraint = Derivation TypeConstraint
  Annotation KindConstraint = Derivation KindConstraint
  Annotation DataAlt        = DataAltInfo -- FIXME should just be a map?
  Annotation a              = Void

type Annotated a = Tag (Source, Maybe (Annotation a)) a

source :: Functor f => (Source -> f Source) -> Annotated a -> f (Annotated a)
source = tag . first

annotation :: Functor f => (Maybe (Annotation a) -> f (Maybe (Annotation a))) -> Annotated a -> f (Annotated a)
annotation = tag . second

split :: Functor f => (Source -> a -> f (Tag (Annotation a) a)) -> Annotated a -> f (Annotated a)
split f ((s, _) :< x) = (\(a :< x) -> ((s, Just a)) :< x) <$> f s x

splitTrivial :: Functor f => (Source -> a -> f a) -> Annotated a -> f (Annotated a)
splitTrivial f ((s, _) :< x) = (\x -> ((s, Nothing) :< x)) <$> f s x

splitPair :: Functor f => (Source -> a -> f (b, Tag (Annotation a) a)) -> Annotated a -> f (b, Annotated a)
splitPair f = runPairT . split (\s a -> PairT (f s a))

phantom :: a -> Annotated a
phantom x = (Phantom, Nothing) :< x

as :: a -> Annotation a -> Annotated a
as x a = (Phantom, Just a) :< x

-- TODO should this be somewhere else?
data Derivation a = Root String
                  | Antecedent (Annotated a)

instance Pretty (Annotated a) => Pretty (Derivation a) where
  pretty (Root r)       = "\n|-> (" <> pretty r <> ")"
  pretty (Antecedent a) = "\n|-> " <> pretty a

data DataAltInfo = DataAltInfo (Annotated QType) (Maybe (Annotated Type)) (Annotated Type)

instance (Pretty (Annotated Type), Pretty (Annotated QType)) => Pretty DataAltInfo where
  pretty (DataAltInfo qt at rt) = pretty qt
