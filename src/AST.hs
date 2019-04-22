module AST
  ( DataAlt(..)
  , Decl(..)
  , Exp(..)
  , Lit(..)
  , Op
  , Tok(..)
  , Pat(..)
  , Program(..)
  , QString(..)
  , Stmt(..)
  ) where

import           Common
import           Kind
import           Record
import           Type

data Decl a = DeclData Name (Maybe (Annotated a TyPat)) [Annotated a DataAlt]
            | DeclFun Name [Annotated a Pat] (Annotated a Exp) -- ^Parsing only
            | DeclSig Name (Annotated a Type) -- ^Parsing only
            | DeclVar Name (Maybe (Annotated a Type)) (Annotated a Exp)

data DataAlt a = DataAlt Name (Annotated a Type)

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

-- |Parsing only
type Op = QString

-- |Parsing only
data Tok a = TExp (Annotated a Exp)
           | TOp Op

-- |AST for Literals
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

data Program a = Program [Annotated a Decl]

data QString = QString { qualification :: [String], name :: String }
  deriving (Ord, Eq)

instance Show QString where
  show s = intercalate "." (qualification s ++ [name s])

data Stmt a = StmtDecl (Annotated a Decl)
            | StmtExp (Annotated a Exp)

instance Show Lit where
  show (Bool b)   = show b
  show (Char c)   = show c
  show (Int i)    = show i
  show (String s) = show s
