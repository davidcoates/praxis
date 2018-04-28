{-# LANGUAGE FlexibleInstances #-}

module AST
  ( Exp(..)
  , Lit(..)
  , Name
  , litTy
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
           | Let Name (a (Exp a)) (a (Exp a))
           | LetBang Name (a (Exp a))
           | Signature (a (Exp a)) Type

-- |AST for Literals
data Lit = Int Int
         | Bool Bool
         | Char Char
         | String String

--class Annotatable b where
--  tmap :: (a -> a) -> a (b a) -> a (b a)

instance DeepTagFunctor Exp where
  tmap' f (If a b c)  = If (tmap f a) (tmap f b) (tmap f c)
  tmap' f (Apply a b) = Apply (tmap f a) (tmap f b)
  tmap' f (Let n a b) = Let n (tmap f a) (tmap f b)
  tmap' f (LetBang n e)   = LetBang n (tmap f e)
  tmap' f (Signature e t) = Signature (tmap f e) t
  tmap' f x               = x

litTy :: Lit -> Pure
litTy = TyPrim . litTy'
  where litTy' (Int _) = TyInt
        litTy' (Bool _) = TyBool
        litTy' (Char _) = TyChar
        litTy' (String _) = TyString

instance Show Lit where
  show (Int i)    = show i
  show (Bool b)   = show b
  show (Char c)   = show c
  show (String s) = show s

-- |Showing ASTs
instance Show a => TreeString (Tagged a Exp) where
  treeString = treeRec $ \x -> case x of
    If x y z      -> Node ("[if]"              ) [treeString x, treeString y, treeString z]
    Lit lit       -> Node (show lit            ) []
    Var s         -> Node (s                   ) []
  --   Apply a e x     -> let (n, b) = compress e in
  --                               Node (n                    ) (b ++ [treeString x])
    Apply f x     -> Node ("[$]"               ) [treeString f, treeString x]
    Let n x y     -> Node ("[let " ++ n ++ "]" ) [treeString x, treeString y]
    LetBang n e   -> Node ("[let " ++ n ++ "!]") [treeString e]
    Signature e t -> Node (":: " ++ show t     ) [treeString e]

  --compress :: Show a => Exp a -> (String, [Tree String])
  --compress (Var s)            = (s, [])
  --compress (Apply (_ :< e) x) = let (f, y) = compress e in (f, y ++ [treeString x])
  --compress x                  = ("$", [treeString' x])

instance Show a => Show (Tagged a Exp) where
  show = showTree
