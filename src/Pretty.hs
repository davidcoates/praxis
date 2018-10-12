{-# LANGUAGE GADTs #-}

module Pretty
  ( indent
  , indents
  ) where

import           AST
import           Data.Tree        (Tree (..), drawTree)
import           Data.Tree.Pretty (drawVerticalTree)
import           Introspect
import           Record           (showKeys)
import qualified Record           (toList)
import           Source
import           Type

indent :: String -> String
indent = indents . lines

indents :: [String] -> String
indents = unlines . map ("  " ++)


-- TODO it will probably be better to use an unparser instead
{-

infix 1 ~>
(~>) :: a -> b -> (a, b)
x ~> b = (x, b)

tree :: Explorable a => Annotated s a -> Tree (ExAnnotation s, String)
tree (a :< x) = Node (ExAnnotation (w, a), n) bs
  where w = witness (a :< x)
        (n, bs) = tree' w x

tree' :: Explorable a => I a -> a s -> (String, [Tree (ExAnnotation s, String)])

tree' IDataAlt  x = case x of
  _ -> undefined -- FIXME

tree' IDecl x = case x of
  _ -> undefined -- FIXME

tree' IExp x = case x of
  Apply f x    -> "[$]"                ~> [tree f, tree x]
  Case e as    -> "[case _ of]"        ~> tree e : concatMap (\(p, e) -> [tree p, tree e]) as
  Cases as     -> "[cases]"            ~> concatMap (\(p, e) -> [tree p, tree e]) as
  Do ss        -> "[do]"               ~> map tree ss
  If a b c     -> "[if]"               ~> [tree a, tree b, tree c]
  Lambda p e   -> "[\\ _ -> _]"        ~> [tree p, tree e]
  Lit l        -> show l               ~> []
  Record r     -> showKeys r           ~> map (tree . snd) (Record.toList r)
  Read n e     -> "[read " ++ n ++ "]" ~> [tree e]
  Var s        -> s                    ~> []
  Sig e (a, b) -> "[_ : _ # _]"        ~> [tree e, tree a, tree b]

tree'  IPat x = case x of
  _ -> undefined

tree'  IProgram x = case x of
  _ -> undefined

tree'  IQType x = case x of
  _ -> undefined

tree'  IStmt x = case x of
  _ -> undefined

tree'  ITyPat x = case x of
  _ -> undefined

tree'  IType x = case x of
  _ -> undefined

showTree

-- Show a tree structure without annotations
showTree_ ::

showFlat_ ::
instance (TreeString a, Show c, c ~ Annotation s a) => Show (Tag c (a s)) where
  show = strip . drawTree . fmap () treeString
    where strip []     = ""
          strip ['\n'] = ""
          strip [x]    = [x]
          strip (x:xs) = x : strip xs


-}
