{-# LANGUAGE FlexibleInstances #-}

module AST
  ( Decl(..)
  , Exp(..)
  , Lit(..)
  , Name
  , Pat(..)
  , Program(..)
  , QString(..)
  , Stmt(..)
  ) where

import           Data.List        (intercalate)
import           Data.Map         (Map)
import qualified Data.Map         as Map
import           Data.Traversable (sequenceA)
import           Pretty
import           Record
import           Tag
import           Type

data Decl a = DeclVar Name (Maybe (a (Impure QType a))) (a (Exp a))
            | DeclData Name (Maybe (a (TyPat a))) [a (DataAlt a)]

data DataAlt a = DataAlt Name (a (Type a))

data Exp a = Apply (a (Exp a)) (a (Exp a))
           | Case (a (Exp a)) [(a (Pat a), a (Exp a))]
           | Cases [(a (Pat a), a (Exp a))]
           | Do [a (Stmt a)]
           | If (a (Exp a)) (a (Exp a)) (a (Exp a))
           | Lambda (a (Pat a)) (a (Exp a))
           | Lit Lit
           | Read Name (a (Exp a))
           | Record (Record (a (Exp a)))
           | Sig (a (Exp a)) (a (Impure Type a))
           | Var Name

-- |AST for Literals
data Lit = Bool Bool
         | Char Char
         | Int Int
         | String String
  deriving (Eq)

data Pat a = PatAt Name (a (Pat a))
           | PatHole
           | PatLit Lit
           | PatRecord (Record (a (Pat a)))
           | PatVar Name

data Program a = Program [a (Decl a)]

data QString = QString { qualification :: [String], name :: String }
  deriving (Ord, Eq)

data Stmt a = StmtDecl (a (Decl a))
            | StmtExp (a (Exp a))

instance Show QString where
  show s = (if prefix == "" then "" else prefix ++ ".") ++ name s
    where prefix = intercalate "." (qualification s)

instance TagTraversable Decl where
  tagTraverse' f (DeclVar n t e) = (DeclVar n) <$> sequenceA (tagTraverse f <$> t) <*> tagTraverse f e

instance TagTraversable Exp where
  tagTraverse' f x = case x of
    Apply a b   -> Apply <$> tagTraverse f a <*> tagTraverse f b
    Case e alts -> Case <$> tagTraverse f e <*> traverse (\(a,b) -> (,) <$> tagTraverse f a <*> tagTraverse f b) alts
    Cases alts  -> Cases <$> traverse (\(a,b) -> (,) <$> tagTraverse f a <*> tagTraverse f b) alts
    Do ss       -> Do <$> traverse (tagTraverse f) ss
    If a b c    -> If <$> tagTraverse f a <*> tagTraverse f b <*> tagTraverse f c
    Lambda p e  -> Lambda <$> tagTraverse f p <*> tagTraverse f e
    Lit l       -> pure $ Lit l
    Record r    -> Record <$> traverse (tagTraverse f) r
    Read n e    -> Read n <$> tagTraverse f e
    Sig e t     -> Sig <$> tagTraverse f e <*> tagTraverse f t
    Var v       -> pure $ Var v

instance TagTraversable Pat where
  tagTraverse' f x = case x of
    PatAt v p   -> PatAt v <$> tagTraverse f p
    PatHole     -> pure PatHole
    PatLit l    -> pure $ PatLit l
    PatRecord r -> PatRecord <$> traverse (tagTraverse f) r
    PatVar v    -> pure $ PatVar v

instance TagTraversable Program where
  tagTraverse' f (Program ds) = Program <$> sequenceA (map (tagTraverse f) ds)

instance TagTraversable Stmt where
  tagTraverse' f (StmtDecl d) = StmtDecl <$> tagTraverse f d
  tagTraverse' f (StmtExp  e) = StmtExp  <$> tagTraverse f e

instance Show a => TreeString (Tagged a Decl) where
  treeString = treeRec $ \x -> case x of
    DeclVar n t e -> Node ("[decl " ++ n ++ t' ++ " = _]") [treeString e]
      where t' = case t of Just t' -> " : " ++ show t'
                           Nothing -> ""

instance Show a => TreeString (Tagged a Exp) where
  treeString = treeRec $ \x -> case x of
    Apply f x     -> Node "[$]"                      [treeString f, treeString x]
    Case e alts   -> Node "[case _ of]"              (treeString e : map (\(p, e) -> Node "[alt]" [treeString p, treeString e]) alts)
    Cases alts    -> Node "[cases]"                  (map (\(p, e) -> Node "[alt]" [treeString p, treeString e]) alts)
    Do ss         -> Node "[do]"                     (map treeString ss)
    If x y z      -> Node "[if]"                     [treeString x, treeString y, treeString z]
    Lambda p e    -> Node "[\\ _ -> _]"              [treeString p, treeString e]
    Lit lit       -> Node (show lit)                 []
    Record r      -> Node (showKeys r)               (map (treeString . snd) (Record.toList r))
    Read n e      -> Node ("[read " ++ n ++ "]")     [treeString e]
    Var s         -> Node s                          []
    Sig e t       -> Node ("[_ : " ++ show t ++ "]") [treeString e]

instance Show a => TreeString (Tagged a Pat) where
  treeString = treeRec $ \x -> case x of
    PatAt v p   -> Node ("[" ++ v ++ "@]") [treeString p]
    PatHole     -> Node "_"                []
    PatLit l    -> Node (show l)           []
    PatRecord r -> Node (showKeys r)       (map (treeString . snd) (Record.toList r))
    PatVar v    -> Node v                  []

instance Show a => TreeString (Tagged a Program) where
  treeString = treeRec $ \x -> case x of
    Program ds -> Node "[program]" (map treeString ds)

instance Show a => TreeString (Tagged a Stmt) where
  treeString = treeRec $ \x -> case x of
    StmtExp  e -> treeString e
    StmtDecl d -> treeString d

instance Show a => Show (Tagged a Decl) where
  show = showTree

instance Show a => Show (Tagged a Exp) where
  show = showTree

instance Show Lit where
  show (Bool b)   = show b
  show (Char c)   = show c
  show (Int i)    = show i
  show (String s) = show s

instance Show a => Show (Tagged a Pat) where
  show = showTree

instance Show a => Show (Tagged a Program) where
  show = showTree

instance Show a => Show (Tagged a Stmt) where
  show = showTree
