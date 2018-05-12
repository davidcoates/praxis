{-# LANGUAGE FlexibleInstances, KindSignatures #-}

module AST
  ( Program(..)
  , Decl(..)
  , Pat(..)
  , Exp(..)
  , Lit(..)
  , QString(..)
  , Name
  , litTy
  ) where

import Tag
import Type
import Pretty
import Data.Map (Map) -- TODO records
import qualified Data.Map as Map
import Data.List (intercalate)
import Record

data Program a = Program [a (Decl a)]

data Decl a = FunDecl Name (a (Exp a))

data Pat (a :: * -> *) = PatUnit -- TODO records
                       | PatVar Name
                       | PatLit Lit
                       | PatRecord (Record (a (Pat a)))

data Exp a = If (a (Exp a)) (a (Exp a)) (a (Exp a)) -- TODO replace this with Case
           | Case (a (Exp a)) [(a (Pat a), a (Exp a))] -- TODO only need (pat, exp) exp ?
           | Lambda Name (a (Exp a)) -- TODO allow pattern 
           | Record (Record (a (Exp a)))
           | Unit -- TODO: Consider Unit as part of Record?
           | Lit Lit
           | Var Name
           | Apply (a (Exp a)) (a (Exp a))
           | Let Name (a (Exp a)) (a (Exp a)) -- TODO allow pattern
           | LetBang Name (a (Exp a))
           | Signature (a (Exp a)) Type

-- |AST for Literals
data Lit = Int Int
         | Bool Bool
         | Char Char
         | String String

data QString = QString { qualification :: [String], name :: String }
  deriving (Ord, Eq)

instance Show QString where
  show s = (if prefix == "" then "" else prefix ++ ".") ++ name s
    where prefix = intercalate "." (qualification s)

litTy :: Lit -> Pure
litTy = TyPrim . litTy'
  where litTy' (Int _) = TyInt
        litTy' (Bool _) = TyBool
        litTy' (Char _) = TyChar
        litTy' (String _) = TyString

instance DeepTagFunctor Program where
  tmap' f (Program ds)    = Program (map (tmap f) ds)

instance DeepTagFunctor Decl where
  tmap' f (FunDecl n e)   = FunDecl n (tmap f e)

instance DeepTagFunctor Pat where
  tmap' f p = p

instance DeepTagFunctor Exp where
  tmap' f (If a b c)      = If (tmap f a) (tmap f b) (tmap f c)
  tmap' f (Case e alts)   = Case (tmap f e) (map (\(a,b) -> (tmap f a, tmap f b)) alts)
  tmap' f (Lambda n e)    = Lambda n (tmap f e)
  tmap' f (Record r)      = Record (fmap (tmap f) r)
  tmap' f (Apply a b)     = Apply (tmap f a) (tmap f b)
  tmap' f (Let n a b)     = Let n (tmap f a) (tmap f b)
  tmap' f (LetBang n e)   = LetBang n (tmap f e)
  tmap' f (Signature e t) = Signature (tmap f e) t
  tmap' f x               = x

instance Show a => TreeString (Tagged a Program) where
  treeString = treeRec $ \x -> case x of
    Program ds -> Node "[program]" (map treeString ds)

instance Show a => TreeString (Tagged a Decl) where
  treeString = treeRec $ \x -> case x of
    FunDecl n e -> Node (n ++ " = ") [treeString e]

instance Show a => TreeString (Tagged a Pat) where
  treeString = treeRec $ \x -> case x of
    PatUnit  -> Node "()"     []
    PatVar n -> Node n        []
    PatLit l -> Node (show l) []

instance Show a => TreeString (Tagged a Exp) where
  treeString = treeRec $ \x -> case x of
    If x y z      -> Node ("[if]"              ) [treeString x, treeString y, treeString z]
    Case e alts   -> Node ("[case]"            ) (treeString e : map (\(p, e) -> Node "[alt]" [treeString p, treeString e]) alts)
    Lambda n e    -> Node ("\\" ++ n ++ " -> " ) [treeString e]
    Unit          -> Node ("()"                ) []
    Record r      -> Node ("[record]"          ) (map (\(n, e) -> treeString e) (Record.toList r)) -- TODO (show n if it is explicit)
    Lit lit       -> Node (show lit            ) []
    Var s         -> Node (s                   ) []
    Apply f x     -> Node ("[$]"               ) [treeString f, treeString x]
    Let n x y     -> Node ("[let " ++ n ++ "]" ) [treeString x, treeString y]
    LetBang n e   -> Node ("[let " ++ n ++ "!]") [treeString e]
    Signature e t -> Node (": " ++ show t      ) [treeString e]

instance Show Lit where
  show (Int i)    = show i
  show (Bool b)   = show b
  show (Char c)   = show c
  show (String s) = show s

instance Show a => Show (Tagged a Program) where
  show = showTree

instance Show a => Show (Tagged a Decl) where
  show = showTree

instance Show a => Show (Tagged a Pat) where
  show = showTree

instance Show a => Show (Tagged a Exp) where
  show = showTree

