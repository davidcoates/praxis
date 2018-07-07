{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Type
  ( Name
  , Pure(..)
  , Prim(..)
  , Impure(..)
  , Effect(..)
  , Effects
  , Constraint(..)
  , Type(..)
  , share
  ) where

import           Common
import           Effect
import           Record

import           Data.Maybe (fromMaybe)

-- |A *top-level* pure type
data Pure = TyBang Pure              -- ^A read-only reference
          | TyData Name [Pure]       -- ^A fully-applied datatype e.g., TyData "Pair" [TyPrim Int, TyPrim Bool] TODO
          | TyFun Pure Impure        -- ^A function `a -> b # e` is represented as TyFun a (TyImpure b e)
          | TyPrim Prim              -- ^A primitive type -- TODO get rid of this eventually
          | TyRecord (Record Pure)   -- ^A record type
          | TyUni String             -- ^A (pure) type unification variable
          | TyVar String             -- ^A type variable (e.g., a in forall a. a -> a)
          deriving (Ord, Eq)

-- Perhaps ultimately replace this with TyData "Bool" [], TyData "Int" []
data Prim = TyBool | TyChar | TyInt | TyString
          deriving (Ord, Eq)

data Impure = Pure :# Effects
  deriving (Ord, Eq)

data Constraint = Class Name Pure -- TODO: Allow effects and higher kinded types in Classes
                | EqualE Effects Effects -- EfEqual ? EqualEf ?
                | EqualP Pure Pure       -- TyEqual ? EqualTy ?
                -- TODO | CVar Name
                deriving (Ord, Eq)

-- TODO: Allow quantified effects, e.g., map :: forall a b (e :: Effects). (a -> b # e) -> [a] -> [b] # e
data Type = Mono Impure
          | Forall [Constraint] [Name] [Name] Pure
  deriving (Ord, Eq)

instance Show Prim where
  show TyBool   = "Bool"
  show TyChar   = "Char"
  show TyInt    = "Int"
  show TyString = "String"

instance Show Constraint where
  show (Class c t)  = c ++ " (" ++ show t ++ ")"
  show (EqualE e f) = show e  ++ " ~ " ++ show f
  show (EqualP a b) = show a  ++ " ~ " ++ show b

instance Show Pure where
  show (TyBang p)    = "bang(" ++ show p ++ ")"
  show (TyData s ts) = s ++ unwords (map (\t -> parens (p t) (show t)) ts)
    where p t = case t of (TyFun _ _)  -> True -- TODO more robust pretty printing
                          (TyData _ _) -> True
                          _            -> False
  show (TyFun a b)   = parens p (show a) ++ " -> " ++ show b
    where p = case a of (TyFun _ _) -> True
                        _           -> False
  show (TyPrim p)    = show p
  show (TyRecord r)  = show r
  show (TyUni s)     = s
  show (TyVar s)     = s

instance Show Impure where
  show (p :# es) = show p ++ (if es == empty then "" else " # " ++ show es)

instance Show Type where
  show (Mono t) = show t
  show (Forall cs xs es t) = "forall " ++ unwords (xs ++ es) ++ ". " ++ cs' ++ show t
    where cs' = if null cs then "" else "(" ++ unwords  (map show cs) ++ ") => "

parens True  x = "(" ++ x ++ ")"
parens False x = x

share :: Pure -> Constraint
share = Class "Share"
