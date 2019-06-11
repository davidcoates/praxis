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
  , TyPat(..)
  , Type(..)
  , QType(..)

  -- | T2
  , Kind(..)

  -- | Solver
  , KindConstraint(..)
  , TypeConstraint(..)

  , Parse
  , KindCheck
  , TypeCheck

  , Annotation
  , Annotated
  , Parsed
  , Kinded
  , Typed
  , phantom
  , as

  , Derivation(..)
  ) where

import           Common
import           Record

import           Data.Set (Set)

-- |Parsing only
type Op = QString

-- |TODO move this to Common?
data QString = QString { qualification :: [String], name :: String }
  deriving (Ord, Eq)

instance Show QString where
  show s = intercalate "." (qualification s ++ [name s])

instance Show Lit where
  show l = case l of
    Bool b   -> show b
    Char c   -> show c
    Int i    -> show i
    String s -> show s

data Decl a = DeclData Name (Maybe (Annotated a TyPat)) [Annotated a DataAlt]
            | DeclFun Name [Annotated a Pat] (Annotated a Exp) -- ^Parsing only
            | DeclSig Name (Annotated a QType) -- ^Parsing only
            | DeclVar Name (Maybe (Annotated a QType)) (Annotated a Exp)
  deriving (Eq)

data DataAlt a = DataAlt Name (Annotated a Type)
  deriving (Eq)

data Exp a = Apply (Annotated a Exp) (Annotated a Exp)
           | Case (Annotated a Exp) [(Annotated a Pat, Annotated a Exp)]
           | Cases [(Annotated a Pat, Annotated a Exp)]
           | Do [Annotated a Stmt]
           | If (Annotated a Exp) (Annotated a Exp) (Annotated a Exp)
           | Lambda (Annotated a Pat) (Annotated a Exp)
           | Lit Lit
           | Mixfix [Annotated a Tok] -- ^Parsing only
           | Read Name (Annotated a Exp)
           | Record (Record (Annotated a Exp))
           | Sig (Annotated a Exp) (Annotated a Type)
           | Var Name
           | VarBang Name -- ^Parsing only
  deriving (Eq)

data Lit = Bool Bool
         | Char Char
         | Int Int
         | String String
  deriving (Eq)

data Pat a = PatAt Name (Annotated a Pat)
           | PatHole
           | PatLit Lit
           | PatRecord (Record (Annotated a Pat))
           | PatVar Name
  deriving (Eq)

data Program a = Program [Annotated a Decl]
  deriving (Eq)

data Stmt a = StmtDecl (Annotated a Decl)
            | StmtExp (Annotated a Exp)
  deriving (Eq)

-- |Parsing only
data Tok a = TExp (Annotated a Exp)
           | TOp Op
  deriving (Eq)

data TyPat a = TyPatVar Name
             | TyPatPack (Record (Annotated a TyPat))
  deriving (Eq, Ord)

data Type a = TyUni Name                                      -- Compares less than all other types
            | TyApply (Annotated a Type) (Annotated a Type)
            | TyBang (Annotated a Type)
            | TyCon Name
            | TyFlat (Set (Annotated a Type))                 -- Used for constraints
            | TyFun (Annotated a Type) (Annotated a Type)
            | TyPack   (Record (Annotated a Type))            -- ^A type pack with a record kind
            | TyRecord (Record (Annotated a Type))            -- ^A type record : T
            | TyVar Name
  deriving (Eq, Ord)

data QType a = Mono (Annotated a Type)
             | Forall [Name] (Annotated a Type)
  deriving (Eq, Ord)

data Kind a = KindUni Name
            | KindConstraint
            | KindFun (Annotated a Kind) (Annotated a Kind)
            | KindRecord (Record (Annotated a Kind))
            | KindType
  deriving (Eq, Ord)

infixl 8 `TEq`
data TypeConstraint a = Class (Annotated a Type)
                      | TEq (Annotated a Type) (Annotated a Type)
  deriving (Eq, Ord)

data KindConstraint a = KEq (Annotated a Kind) (Annotated a Kind)
  deriving (Eq, Ord)

data Parse
data KindCheck
data TypeCheck

type family Annotation a (b :: * -> *) where
  -- |Parse
  Annotation Parse     a              = ()
  -- |KindCheck
  Annotation KindCheck TyPat          = Kinded Kind
  Annotation KindCheck Type           = Kinded Kind
  Annotation KindCheck KindConstraint = Derivation KindCheck KindConstraint
  Annotation KindCheck a              = ()
  -- |TypeCheck
  Annotation TypeCheck Exp            = Typed Type
  Annotation TypeCheck Pat            = Typed Type
  Annotation TypeCheck TyPat          = Typed Kind
  Annotation TypeCheck Type           = Typed Kind
  Annotation TypeCheck TypeConstraint = Derivation TypeCheck TypeConstraint
  Annotation TypeCheck a              = ()

type Annotated a b = Tag (Source, Annotation a b) (b a)

type Parsed a = Annotated Parse     a
type Kinded a = Annotated KindCheck a
type Typed  a = Annotated TypeCheck a

phantom :: (Annotation a b ~ ()) => b a -> Annotated a b
phantom x = x `as` ()

as :: b a -> Annotation a b -> Annotated a b
as x a = (Phantom, a) :< x

-- TODO should this be somewhere else?
data Derivation s a = Root String
                    | Antecedent (Annotated s a)

instance Pretty (Annotated s a) => Pretty (Derivation s a) where
  pretty (Root r)       = "\n|-> (" <> plain r <> ")"
  pretty (Antecedent a) = "\n|-> " <> pretty a
