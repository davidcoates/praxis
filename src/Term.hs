{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

module Term
  ( Op
  , QString(..)

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
import           Pretty
import           Record

import           Data.Set (Set)

-- |Parsing only
type Op = QString

-- |TODO move this to Common?
data QString = QString { qualification :: [String], name :: String }
  deriving (Ord, Eq)

instance Show QString where
  show s = intercalate "." (qualification s ++ [name s])

data Decl = DeclData Name [Annotated TyPat] [Annotated DataAlt]
          | DeclFun Name [Annotated Pat] (Annotated Exp) -- ^Parsing only
          | DeclSig Name (Annotated QType) -- ^Parsing only
          | DeclVar Name (Maybe (Annotated QType)) (Annotated Exp)

data DataAlt = DataAlt Name [Annotated Type]

data Exp = Apply (Annotated Exp) (Annotated Exp)
         | Case (Annotated Exp) [(Annotated Pat, Annotated Exp)]
         | Cases [(Annotated Pat, Annotated Exp)]
         | Con Name
         | Do [Annotated Stmt]
         | If (Annotated Exp) (Annotated Exp) (Annotated Exp)
         | Lambda (Annotated Pat) (Annotated Exp)
         | Lit Lit
         | Mixfix [Annotated Tok] -- ^Parsing only
         | Read Name (Annotated Exp)
         | Record (Record (Annotated Exp))
         | Sig (Annotated Exp) (Annotated Type)
         | Var Name
         | VarBang Name -- ^Parsing only

data Lit = Bool Bool
         | Char Char
         | Int Int
         | String String
  deriving Eq

instance Show Lit where
  show = \case
    Bool b   -> show b
    Char c   -> show c
    Int i    -> show i
    String s -> show s

data Pat = PatAt Name (Annotated Pat)
         | PatHole
         | PatLit Lit
         | PatRecord (Record (Annotated Pat))
         | PatVar Name
         | PatCon Name [Annotated Pat]

data Program = Program [Annotated Decl]

data Stmt = StmtDecl (Annotated Decl)
          | StmtExp (Annotated Exp)

-- |Parsing only
data Tok = TExp (Annotated Exp)
         | TOp Op

data TyOp = TyOpUni Name
          | TyOpBang
          | TyOpId
          | TyOpVar Name
  deriving (Eq, Ord)

data TyPat = TyPatVar Name
  deriving (Eq, Ord)

data Type = TyUni Name                                -- Compares less than all other types
          | TyApply (Annotated Type) (Annotated Type)
          | TyCon Name
          | TyFun (Annotated Type) (Annotated Type)
          | TyRecord (Record (Annotated Type))        -- A type record : T
          | TyOp (Annotated TyOp) (Annotated Type)
          | TyVar Name
  deriving (Eq, Ord)

data QTyVar = QTyVar Name | QTyOpVar Name
  deriving (Eq, Ord)

data QType = Mono (Annotated Type)
           | Forall [QTyVar] (Annotated Type)
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
  Annotation DataAlt        = DataAltInfo
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

data DataAltInfo = DataAltInfo [Name] (Annotated QType) [Annotated Type] (Annotated Type)

instance (Pretty (Annotated Type), Pretty (Annotated QType)) => Pretty DataAltInfo where
  pretty (DataAltInfo ns ct args rt) = pretty ct
