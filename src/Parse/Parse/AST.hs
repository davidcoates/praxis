{-# LANGUAGE FlexibleInstances #-}

module Parse.Parse.AST
  ( module AST
  , AST
  , Annotation
  , Annotated
  , Exp(..)
  , Decl(..)
  , Op
  , Tok(..)
  ) where

import Data.Tree (Tree(..))
import AST (Lit(..), Name, Annotate(..), TreeShow(..))
import Source
import Type

type Annotation = Source
type Annotated a = a Annotation

type AST = Annotated Exp

data Exp a = If a (Exp a) (Exp a) (Exp a)
           | Lit a Lit
           | Var a Name
           | Apply a (Exp a) (Exp a)
           | Infix a [Tok a]
           | Let a [Decl a] (Exp a)
           | Signature a (Exp a) Type

data Decl a = Bang a Name
            | FunType a Name Type
            | FunDecl a Name (Annotated Exp)

-- Tok is used for structuring infix expressions.
-- It represents a token in an unstructure infix expression, where a token is either an expression, a binary operator, or prefix negation.

type Op = String -- TODO qualified string

data Tok a = TExp a (Exp a)
           | TOp a Op
           | TNeg a -- TODO remove this after integrating mixfix parser


instance Show a => TreeShow (Decl a) where
  treeString (Bang a n)      = Node ("!" ++ n              ++ " @ " ++ show a) []
  treeString (FunType a f t) = Node (f ++ " :: " ++ show t ++ " @ " ++ show a) []
  treeString (FunDecl a f e) = Node (f ++ " = "            ++ " @ " ++ show a) [treeString e]

instance Show a => TreeShow (Exp a) where
  treeString (If a x y z)      = Node ("[if]"          ++ " @ " ++ show a) [treeString x, treeString y, treeString z]
  treeString (Lit a lit)       = Node (show lit        ++ " @ " ++ show a) []
  treeString (Var a v)         = Node (show v          ++ " @ " ++ show a) []
  treeString (Let a ds e)      = Node ("[let]"         ++ " @ " ++ show a) (map treeString ds ++ [treeString e])
  treeString (Signature a e t) = Node (":: " ++ show t ++ " @ " ++ show a) [treeString e]
  treeString (Infix a ts)      = Node ("[infix]"       ++ " @ " ++ show a) (map tokShow ts)
    where tokShow (TExp a e) = treeString e
          tokShow (TOp a o)  = Node (o           ++ " @ " ++ show a) []
          tokShow (TNeg a)   = Node ("prefix[-]" ++ " @ " ++ show a) []

instance Show a => Show (Decl a) where
  show = showTree

instance Show a => Show (Exp a) where
  show = showTree
