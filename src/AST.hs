{-# LANGUAGE FlexibleInstances #-}

module AST
  ( Exp(..)
  , Decl(..)
  , Lit(..)
  , Name
  , Annotate(..)
  , TreeShow(..)
  ) where

import Data.Tree (Tree(..))
import Data.Tree.Pretty (drawVerticalTree)
import Text.Parsec.String (Parser)
import Type
import Control.Lens (Lens')

{-
-- TODO module import, export
data Program a = Program [TopDecl a]

-- TODO type, data, newtype, class, instance, default, foreign
type TopDecl a = Decl a

data Decl a = ...
-}

data Exp a = If a (Exp a) (Exp a) (Exp a)
           | Lit a Lit
           | Var a Name
           | Apply a (Exp a) (Exp a)
           | Let a (Decl a) (Exp a)
           | LetBang a Name (Exp a)
           | Signature a (Exp a) Type

data Decl a = FunDecl a Name (Exp a)
            -- TODO: Fixity declarations


-- |AST for Literals
data Lit = Integer Integer
         | Bool Bool

instance Show Lit where
  show (Integer i) = show i
  show (Bool b) = show b


-- |Getting and setting annotations to ASTs
class Annotate e where
  annotation :: Lens' (e a) a

instance Annotate Exp where
  annotation f (If a x y z)      = (flip fmap) (f a) (\a -> If a x y z)
  annotation f (Lit a l)         = (flip fmap) (f a) (\a -> Lit a l)
  annotation f (Var a v)         = (flip fmap) (f a) (\a -> Var a v)
  annotation f (Apply a x y)     = (flip fmap) (f a) (\a -> Apply a x y)
  annotation f (LetBang a d e)   = (flip fmap) (f a) (\a -> LetBang a d e)
  annotation f (Signature a e t) = (flip fmap) (f a) (\a -> Signature a e t)

instance Annotate Decl where
  annotation f (FunDecl a n e) = (flip fmap) (f a) (\a -> FunDecl a n e)


-- |Showing ASTs
class TreeShow a where
  treeString :: a -> Tree String
  showTree :: a -> String
  showTree = drawVerticalTree . treeString

instance Show a => TreeShow (Decl a) where
  treeString (FunDecl a f e) = Node ("[fun " ++ f ++ "]" ++ " @ " ++ show a) [treeString e]

instance Show a => TreeShow (Exp a) where
  treeString (If a x y z)      = Node ("[if]"               ++ " @ " ++ show a) [treeString x, treeString y, treeString z]
  treeString (Lit a lit)       = Node (show lit             ++ " @ " ++ show a) []
  treeString (Var a s)         = Node (s                    ++ " @ " ++ show a) []
  -- treeString (Apply a e x)     = let (n, b) = compress e in
  --                               Node (n                    ++ " @ " ++ show a) (b ++ [treeString x])
  treeString (Apply a f x)     = Node ("[$]"                ++ " @ " ++ show a) [treeString f, treeString x]
  treeString (Let a d e)       = Node ("[let]"              ++ " @ " ++ show a) [treeString d, treeString e]
  treeString (LetBang a n e)   = Node ("[let " ++ n ++ "!]" ++ " @ " ++ show a) [treeString e]
  treeString (Signature a e t) = Node (":: " ++ show t      ++ " @ " ++ show a) [treeString e]

  --compress :: Show a => Exp a -> (String, [Tree String])
  --compress (Var s)            = (s, [])
  --compress (Apply (_ :< e) x) = let (f, y) = compress e in (f, y ++ [treeString x])
  --compress x                  = ("$", [treeString' x])

instance Show a => Show (Exp a) where
  show = showTree

instance Show a => Show (Decl a) where
  show = showTree

