{-# LANGUAGE FlexibleInstances #-}

module Parse.Parse.AST
  ( Annotation
  , Annotated(..)
  , Decl(..)
  , Exp(..)
  , Op
  , Pat(..)
  , Program(..)
  , Stmt(..)
  , Tok(..)
  ) where

import           AST    (Lit (..), Pat (..), QString)
import           Common
import           Record
import           Type

data Decl a = DeclFun Name [Annotated a Pat] (Annotated a Exp)
            | DeclSig Name (Annotated a QType)

data Exp a = Apply (Annotated a Exp) (Annotated a Exp)
           | Case (Annotated a Exp) [(Annotated a Pat, Annotated a Exp)]
           | Cases [(Annotated a Pat, Annotated a Exp)]
           | Do [Annotated a Stmt]
           | If (Annotated a Exp) (Annotated a Exp) (Annotated a Exp)
           | Lit Lit
           | Mixfix [Annotated a Tok]
           | Read Name (Annotated a Exp)
           | Record (Record (Annotated a Exp))
           | Sig (Annotated a Exp) (Annotated a Type)
           | Var Name
           | VarBang Name

type Op = QString

data Program a = Program [Annotated a Decl]

data Stmt a = StmtDecl (Annotated a Decl)
            | StmtExp (Annotated a Exp)

data Tok a = TExp (Annotated a Exp)
           | TOp Op

{-
instance TreeString (Annotated Decl) where
  treeString = treeRec $ \x -> case x of
    DeclFun f ps e -> Node (f ++ show ps ++ " = ") [treeString e]
    DeclSig f t    -> Node (f ++ " : " ++ show t)  []

instance TreeString (Annotated Exp) where
  treeString = treeRec $ \x -> case x of
    Apply e1 e2 -> Node "[$]"                  [treeString e1, treeString e2]
    Case e alts -> Node "[case]"               (treeString e : map (\(p, e) -> Node "[alt]" [treeString p, treeString e]) alts)
    Cases alts -> Node "[cases]"               (map (\(p, e) -> Node "[alt]" [treeString p, treeString e]) alts)
    Do ss       -> Node "[do]"                 (map treeString ss)
    If x y z    -> Node "[if]"                 [treeString x, treeString y, treeString z]
    Lit l       -> Node (show l)               []
    Mixfix ts   -> Node "[mixfix]"             (map tokShow ts)
    Read v e    -> Node ("[read " ++ v ++ "]") [treeString e]
    Record r    -> Node (showKeys r)           (map (treeString . snd) (Record.toList r))
    Sig e t     -> Node (": " ++ show t)       [treeString e]
    Var v       -> Node v                      []
    VarBang v   -> Node ("!" ++ v)             []
    where tokShow :: Annotated Tok -> Tree String
          tokShow (a :< TExp e) = treeString e -- Don't show redundant source (same as source of e)
          tokShow op            = treeRec (\(TOp o) -> Node (show o) []) op

instance TreeString (Annotated Program) where
  treeString = treeRec $ \x -> case x of
    Program ds -> Node "[program]" (map treeString ds)

instance TreeString (Annotated Stmt) where
  treeString = treeRec $ \x -> case x of
    StmtExp e  -> treeString e
    StmtDecl d -> treeString d

instance Show (Annotated Decl) where
  show = showTree

instance Show (Annotated Exp) where
  show = showTree

instance Show (Annotated Program) where
  show = showTree

instance Show (Annotated Stmt) where
  show = showTree

-}
