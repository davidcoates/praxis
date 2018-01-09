{-# LANGUAGE FlexibleInstances #-}

module AST
  ( Error(..)
  , SourcePos(..)
  , getPosition
  , indent
  , Lit(..)
  , Prim(..)
  , Exp(..)
  , Tag(..)
  , Annotate
  , Praxis
  , PraxisTail
  , mapExp
  , lift
  , tagTree
  , TreeShow(..)
  ) where

import Data.Tree (Tree(..))
import Data.Tree.Pretty (drawVerticalTree)
import Text.Parsec.Pos (sourceName, sourceLine, sourceColumn)
import qualified Text.Parsec.Pos as Parsec (SourcePos)
import Text.Parsec.String (Parser)
import qualified Text.ParserCombinators.Parsec.Prim as Parsec (getPosition)

newtype SourcePos = SourcePos Parsec.SourcePos

instance Show SourcePos where
  show (SourcePos p) = sourceName p ++ ":" ++ show (sourceLine p) ++ ":" ++ show (sourceColumn p)

data Error a = Error { pos :: SourcePos, stage :: String,  message :: a }

indent :: String -> String
indent = unlines . map ("  " ++) . lines

instance Show a => Show (Error a) where
  show e = "error in stage <<" ++ stage e ++ ">> at " ++ show p ++ indent (show (message e))
         where p = pos e

getPosition = SourcePos <$> Parsec.getPosition


data Lit = Integer Integer | Bool Bool

instance Show Lit where
  show (Integer i) = show i

data Exp a = If (a (Exp a)) (a (Exp a)) (a (Exp a))
           | Lit Lit
           | Fun String
           | Apply (a (Exp a)) (a (Exp a))
           | Prim Prim

mapExp :: (a -> b) -> Annotate a Exp -> Annotate b Exp
mapExp f (p :< x) = f p :< mapExp' x
  where mapExp' (If x y z)  = If (mapExp f x) (mapExp f y) (mapExp f z)
        mapExp' (Lit l)     = Lit l
        mapExp' (Fun s)     = Fun s
        mapExp' (Apply a b) = Apply (mapExp f a) (mapExp f b)
        mapExp' (Prim p)    = Prim p

-- Primitive terms such as prefix negation
data Prim = Neg

instance Show Prim where
  show Neg = "[-]"

data Tag a b = a :< b

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

tagTree :: Show a => (b -> Tree String) -> Tag a b -> Tree String
tagTree f (a :< x) = let Node y bs = f x in Node (show a ++ " :< " ++ y) bs

class TreeShow b where
  toTreeString :: Show a => Annotate a b -> Tree String
  showTree :: Show a => Annotate a b -> String
  showTree = drawVerticalTree . toTreeString

instance TreeShow Exp where
  toTreeString = treeShow
      where treeShow :: Show a => Annotate a Exp -> Tree String
            treeShow = tagTree treeShow'
            treeShow' (If x y z)  = Node "[if]" [treeShow x, treeShow y, treeShow z]
            treeShow' (Lit lit)   = Node (show lit) []
            treeShow' (Fun s)     = Node s []
            treeShow' (Prim p)    = Node (show p) []
            treeShow' (Apply (_ :< e) x) = let (a, b) = compress e in Node a (b ++ [treeShow x])

            compress :: Show a => Exp (Tag a) -> (String, [Tree String])
            compress (Prim p)           = (show p, [])
            compress (Fun s)            = (s, [])
            compress (Apply (_ :< e) x) = let (f, y) = compress e in (f, y ++ [treeShow x])
            compress x                  = ("$", [treeShow' x])

instance Show (Praxis Exp) where
  show t = showTree t
