{-# LANGUAGE FlexibleInstances #-}

module AST 
  ( Lit(..)
  , Prim(..)
  , Exp(..)
  , Tag(..)
  , Annotate
  , Praxis
  , PraxisTail
  , lift
  , tagTree
  ) where

import Data.Tree (Tree(..))
import Data.Tree.Pretty (drawVerticalTree)
import Text.Parsec.Pos (SourcePos)
import Text.Parsec.String (Parser)
import Text.ParserCombinators.Parsec.Prim (getPosition)

data Lit = Integer Integer

instance Show Lit where
  show (Integer i) = show i

data Exp a = If (a (Exp a)) (a (Exp a)) (a (Exp a))
           | Lit Lit 
           | Fun String
           | Apply (a (Exp a)) (a (Exp a))
           | Prim Prim

-- Primitive terms such as prefix negation
data Prim = Neg

instance Show Prim where
  show Neg = "[-]"

data Tag a b = a :< b 

tagTree :: Show a => (b -> Tree String) -> Tag a b -> Tree String
tagTree f (a :< x) = let Node y bs = f x in Node (show a ++ " :< " ++ y) bs

{-
instance Functor (Tag a) where
  fmap f (a :< x) = a :< f x
-}

type Annotate a b = Tag a (b (Tag a))

type Praxis a = Annotate SourcePos a
type PraxisTail a = a (Tag SourcePos) -- Praxis a without the top tag


lift :: Parser a -> Parser (Tag SourcePos a)
lift f = do
  p <- getPosition
  x <- f
  return (p :< x)

class TreeShow a where
  treeShow :: a -> Tree String

instance Show a => TreeShow (Annotate a Exp) where
  treeShow = tagTree treeShow'
    where treeShow' (If x y z)  = Node "[if]" [treeShow x, treeShow y, treeShow z]
          treeShow' (Lit lit)   = Node (show lit) []
          treeShow' (Fun s)     = Node s []
          treeShow' (Prim p)    = Node (show p) []
          treeShow' (Apply (_ :< e) x) = let (a, b) = compress e in Node a (b ++ [treeShow x])

          compress :: Show a => Exp (Tag a) -> (String, [Tree String])
          compress (Prim p)           = (show p, [])
          compress (Fun s)            = (s, [])
          compress (Apply (_ :< e) x) = let (f, y) = compress e in (f, y ++ [treeShow x])
          compress x                  = ("$", [treeShow' x])

instance Show a => Show (Annotate a Exp) where
  show = drawVerticalTree . treeShow

