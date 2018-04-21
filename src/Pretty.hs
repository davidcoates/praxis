module Pretty
  ( indent
  , indents
  , TreeString(..)
  , Tree(..)
  , showTree
  , treeRec
  ) where

import Data.Tree (Tree(..))
import Data.Tree.Pretty (drawVerticalTree)
import Tag
import Source

indent :: String -> String
indent = indents . lines

indents :: [String] -> String
indents = unlines . map ("  " ++)

class TreeString a where
  treeString :: a -> Tree String

showTree :: TreeString a => a -> String
showTree = drawVerticalTree . treeString

treeRec :: Show a => (b (Tag a) -> Tree String) -> Tagged a b -> Tree String
treeRec f (a :< x) = case f x of Node n bs -> Node (n ++ " @ " ++ show a) bs
