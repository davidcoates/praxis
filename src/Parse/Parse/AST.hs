{-# LANGUAGE FlexibleInstances #-}

module Parse.Parse.AST
  ( module AST
  , AST
  , Annotated
  , Exp(..)
  , Decl(..)
  , Op
  , Tok(..)
  ) where

import Pretty
import AST (Lit(..), Name)
import Source
import Tag
import Type

type Annotated a = Tagged Source a

type AST = Annotated Exp

data Exp a = If (a (Exp a)) (a (Exp a)) (a (Exp a))
           | Lit Lit
           | Var Name
           | Apply (a (Exp a)) (a (Exp a))
           | Infix [a (Tok a)]
           | Let (a (Decl a)) (a (Exp a)) -- TODO: multiple bindings
           | Signature (a (Exp a)) Type

data Decl a = Bang Name -- TODO Patterns
            | FunType Name Type
            | FunDecl Name (a (Exp a))

type Op = String -- TODO qualified string?

data Tok a = TExp (a (Exp a))
           | TOp Op

instance TreeString (Annotated Decl) where
  treeString = treeRec $ \x -> case x of
    Bang n      -> Node ("!" ++ n)              []
    FunType f t -> Node (f ++ " :: " ++ show t) []
    FunDecl f e -> Node (f ++ " = ")            [treeString e]

instance TreeString (Annotated Exp) where
  treeString = treeRec $ \x -> case x of
    If x y z      -> Node "[if]"            [treeString x, treeString y, treeString z]
    Lit l         -> Node (show l)          []
    Var v         -> Node (show v)          []
    Let d e       -> Node "[let]"           [treeString d, treeString e]
    Signature e t -> Node (":: " ++ show t) [treeString e]
    Infix ts      -> Node "[infix]"         (map tokShow ts)
    where tokShow :: Annotated Tok -> Tree String
          tokShow (a :< TExp e) = treeString e -- Don't show redundant source (same as source of e)
          tokShow op            = treeRec (\(TOp o) -> Node o []) op

instance Show (Annotated Decl) where
  show = showTree

instance Show (Annotated Exp) where
  show = showTree
