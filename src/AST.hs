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

import           Control.Applicative (liftA2, liftA3)
import           Data.List           (intercalate)
import           Data.Map            (Map)
import qualified Data.Map            as Map
import           Data.Traversable    (sequenceA)
import           Pretty
import           Record
import           Tag
import           Type

data Decl a = DeclFun Name (Maybe (a (Impure a))) Int [([a (Pat a)], a (Exp a))]

{- TODO
            | DeclData Name (Maybe (a (DataKind a))) [a (DataAlt a)]

data DataKind a = DataKindVar Name
                | DataKindRecord (Record (a (DataKind a)))
                | DataKindSignature (a (DataKind a)) Kind


data DataAlt a =
-}

data Exp a = Apply (a (Exp a)) (a (Exp a))
           | Case (a (Exp a)) [(a (Pat a), a (Exp a))]
           | Do [a (Stmt a)]
           | If (a (Exp a)) (a (Exp a)) (a (Exp a))
           | Lambda (a (Pat a)) (a (Exp a))
           | Lit Lit
           | Read Name (a (Exp a))
           | Record (Record (a (Exp a)))
           | Sig (a (Exp a)) (a (Impure a))
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
  tagTraverse' f (DeclFun n t i ds) = liftA2 (\t ds -> DeclFun n t i ds) (sequenceA (tagTraverse f <$> t)) (sequenceA (map (\(ps, e) -> liftA2 (,) (sequenceA (map (tagTraverse f) ps)) (tagTraverse f e)) ds))

instance TagTraversable Exp where
  tagTraverse' f (Apply a b)   = liftA2 Apply (tagTraverse f a) (tagTraverse f b)
  tagTraverse' f (Case e alts) = liftA2 Case (tagTraverse f e) (sequenceA (map (\(a,b) -> liftA2 (,) (tagTraverse f a) (tagTraverse f b)) alts))
  tagTraverse' f (Do ss)       = Do <$> sequenceA (map (tagTraverse f) ss)
  tagTraverse' f (If a b c)    = liftA3 If (tagTraverse f a) (tagTraverse f b) (tagTraverse f c)
  tagTraverse' f (Lambda p e)  = liftA2 Lambda (tagTraverse f p) (tagTraverse f e)
  tagTraverse' f (Lit l)       = pure $ Lit l
  tagTraverse' f (Record r)    = Record <$> sequenceA (fmap (tagTraverse f) r)
  tagTraverse' f (Read n e)    = Read n <$> tagTraverse f e
  tagTraverse' f (Sig e t)     = liftA2 Sig (tagTraverse f e) (tagTraverse f t)
  tagTraverse' f (Var v)       = pure $ Var v

instance TagTraversable Pat where
  tagTraverse' f (PatAt v p)   = PatAt v <$> tagTraverse f p
  tagTraverse' f PatHole       = pure PatHole
  tagTraverse' f (PatLit l)    = pure $ PatLit l
  tagTraverse' f (PatRecord r) = PatRecord <$> sequenceA (fmap (tagTraverse f) r)
  tagTraverse' f (PatVar v)    = pure $ PatVar v

instance TagTraversable Program where
  tagTraverse' f (Program ds) = Program <$> sequenceA (map (tagTraverse f) ds)

instance TagTraversable Stmt where
  tagTraverse' f (StmtDecl d) = StmtDecl <$> tagTraverse f d
  tagTraverse' f (StmtExp  e) = StmtExp  <$> tagTraverse f e

instance Show a => TreeString (Tagged a Decl) where
  treeString = treeRec $ \x -> case x of
    DeclFun n t i ds -> Node ("[decl " ++ n ++ t' ++ "]") (map (\(ps, e) -> Node "[_* = _]" (map treeString ps ++ [treeString e])) ds)
      where t' = case t of Just t' -> " : " ++ show t'
                           Nothing -> ""

instance Show a => TreeString (Tagged a Exp) where
  treeString = treeRec $ \x -> case x of
    Apply f x     -> Node "[$]"                      [treeString f, treeString x]
    Case e alts   -> Node "[case]"                   (treeString e : map (\(p, e) -> Node "[alt]" [treeString p, treeString e]) alts)
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
