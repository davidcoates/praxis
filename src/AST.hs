{-# LANGUAGE FlexibleInstances #-}

module AST
  ( Exp(..)
  , Decl(..)
  , Lit(..)
  , Name
  ) where

import Tag
import Type
import Pretty

{-
-- TODO module import, export
data Program a = Program [TopDecl a]

-- TODO type, data, newtype, class, instance, default, foreign
type TopDecl a = Decl a

data Decl a = ...
-}

data Exp a = If (a (Exp a)) (a (Exp a)) (a (Exp a))
           | Lit Lit
           | Var Name
           | Apply (a (Exp a)) (a (Exp a))
           | Let (a (Decl a)) (a (Exp a))
           | LetBang Name (a (Exp a))
           | Signature (a (Exp a)) Type

data Decl a = FunDecl Name (a (Exp a))
            -- TODO: Fixity declarations

-- |AST for Literals
data Lit = Integer Integer
         | Bool Bool

instance Show Lit where
  show (Integer i) = show i
  show (Bool b) = show b

-- |Showing ASTs
instance Show a => TreeString (Tagged a Decl) where
  treeString = treeRec $ \x -> case x of
    FunDecl f e -> Node ("[fun " ++ f ++ "]") [treeString e]

instance Show a => TreeString (Tagged a Exp) where
  treeString = treeRec $ \x -> case x of
    If x y z      -> Node ("[if]"              ) [treeString x, treeString y, treeString z]
    Lit lit       -> Node (show lit            ) []
    Var s         -> Node (s                   ) []
  --   Apply a e x     -> let (n, b) = compress e in
  --                               Node (n                    ) (b ++ [treeString x])
    Apply f x     -> Node ("[$]"               ) [treeString f, treeString x]
    Let d e       -> Node ("[let]"             ) [treeString d, treeString e]
    LetBang n e   -> Node ("[let " ++ n ++ "!]") [treeString e]
    Signature e t -> Node (":: " ++ show t     ) [treeString e]

  --compress :: Show a => Exp a -> (String, [Tree String])
  --compress (Var s)            = (s, [])
  --compress (Apply (_ :< e) x) = let (f, y) = compress e in (f, y ++ [treeString x])
  --compress x                  = ("$", [treeString' x])

instance Show a => Show (Tagged a Decl) where
  show = showTree

instance Show a => Show (Tagged a Exp) where
  show = showTree
