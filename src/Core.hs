module Core
  (
  ) where

import           Common
import           Praxis
import qualified Term


data Reason = BindFail
            | NonExhaustiveCase
            | NonExhaustiveSwitch
  deriving Show

data Prim1 = INeg
           | BNeg
  deriving Show

data Prim2 = IAdd
           | ISub
           | IMul
           | IDiv
           | BOr
           | BAnd
           | BXor
  deriving Show

data Pat = PatAt Name Pat
         | PatCon Name (Maybe Pat)
         | PatHole
         | PatLit Term.Lit
         | PatPair Pat Pat
         | PatUnit
         | PatVar Name
  deriving Show

data Module = Module { name :: Name, defs :: [Def] }
  deriving Show

type Ty = Name

data Def = Def [Ty] Name Exp
         | DefRec [([Ty], Name, Exp)] Exp
  deriving Show

data Bind = Bind Pat Exp
  deriving Show

data Stmt = StmtBind Bind
          | StmtExp Exp
  deriving Show

data Exp = Apply Exp Exp
         | ApplyPrim1 Prim1 Exp
         | ApplyPrim2 Prim2 (Exp, Exp)
         | Case Exp [(Pat, Exp)] Source
         | ConApply Name (Maybe Exp)
         | Do [Stmt]
         | Lit Term.Lit
         | Where Exp [Def]
         | Lambda [Name] Pat Exp Source
         | Let Bind Exp
         | Pair Exp Exp
         | Unit
         | Switch [(Exp, Exp)] Source
         | Var Name
         | Specialise Name [Name]
  deriving Show
