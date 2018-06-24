{-# LANGUAGE FlexibleInstances, KindSignatures #-}

module Parse.Parse.AST
  ( module AST
  , AST
  , Annotated
  , Program(..)
  , Decl(..)
  , Pat(..)
  , Exp(..)
  , Op
  , Tok(..)
  ) where

import Pretty
import AST (Lit(..), Name, QString, Pat(..))
import Source
import Tag
import Type

type Annotated a = Tagged Source a

type AST = Annotated Program

data Program a = Program [a (Decl a)]

-- This is a bit dodgy. We use Decl a both for top-level declarations and let declarations
-- However, Bang will never appear in top-level declarations.
data Decl a = Bang Name
            | FunType Name Type
            | DeclFun Name [a (Pat a)] (a (Exp a))

-- TODO Records
data Exp a = If (a (Exp a)) (a (Exp a)) (a (Exp a))
           | Case (a (Exp a)) [(a (Pat a), a (Exp a))]
           | Lit Lit
           | Var Name
           | Unit
           | Apply (a (Exp a)) (a (Exp a))
           | Infix [a (Tok a)]
           | Let [a (Decl a)] (a (Exp a))
           | Signature (a (Exp a)) Type

type Op = QString

-- TODO do we really need Annotated Tok?
data Tok a = TOp Op
           | TExp (a (Exp a))

instance TreeString (Annotated Program) where
  treeString = treeRec $ \x -> case x of
    Program ds -> Node "[program]" (map treeString ds)

instance TreeString (Annotated Decl) where
  treeString = treeRec $ \x -> case x of
    Bang n         -> Node ("!" ++ n)              []
    FunType f t    -> Node (f ++ " :: " ++ show t) []
    DeclFun f ps e -> Node (f ++ show ps ++ " = ") [treeString e]

instance TreeString (Annotated Exp) where
  treeString = treeRec $ \x -> case x of
    If x y z      -> Node ("[if]"         ) [treeString x, treeString y, treeString z]
    Case e alts   -> Node ("[case]"       ) (treeString e : map (\(p, e) -> Node "[alt]" [treeString p, treeString e]) alts)
    Unit          -> Node ("()"           ) []
    Lit l         -> Node (show l         ) []
    Var v         -> Node (v              ) []
    Apply e1 e2   -> Node ("[$]"          ) [treeString e1, treeString e2]
    Let ds e      -> Node ("[let]"        ) (map treeString ds ++ [treeString e])
    Signature e t -> Node (":: " ++ show t) [treeString e]
    Infix ts      -> Node ("[infix]"      ) (map tokShow ts)
    where tokShow :: Annotated Tok -> Tree String
          tokShow (a :< TExp e) = treeString e -- Don't show redundant source (same as source of e)
          tokShow op             = treeRec (\(TOp o) -> Node (show o) []) op

instance Show (Annotated Program) where
  show = showTree

instance Show (Annotated Decl) where
  show = showTree

instance Show (Annotated Exp) where
  show = showTree
