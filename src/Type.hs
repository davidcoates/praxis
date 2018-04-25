module Type
  ( Name
  , Effect(..)
  , Effects
  , Pure(..)
  , Prim(..)
  , Type(..)
  , Constraint(..)
  , QPure(..)
  , subsEffects
  , subsType
  , subsPure
  , subsConstraint
  , shareC
  , dropC
  , pureTy
  , mono
  ) where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)

type Name = String

{-|
  Effects functions as a *flat set* of effect.
  An effect unification variable can be replaced with a flat set of effects, e.g.,
  { EfUni α, EfString "Read IO" } if α ~> { Ef "WriteIO", Ef "ReadHeap" } then the result is { Ef "WriteIO", Ef "ReadHeap", Ef "Read IO" }
-}
data Effect = Ef String              -- ^A concrete effect e.g., Eg `ReadIO`
            | EfUni String           -- ^An effect unification variable
            deriving (Ord, Eq)

type Effects = Set Effect

-- |A *top-level* pure type
data Pure = TyPrim Prim              -- ^A primitive type
          | TyUni String             -- ^A (pure) type unification variable
          | TyFun Pure Type          -- ^A function `a -> b # e` is represented as TyFun a (TyImpure b e)
          | TyData String [Pure]     -- ^A fully-applied datatype e.g., TyData "Pair" [TyPrim Int, TyPrim Bool]
          | TyVar String             -- ^A type variable (e.g., a in forall a. a -> a)
          deriving (Ord, Eq)

-- Perhaps ultimately replace this with TyData "Bool" [], TyData "Int" []
data Prim = TyBool | TyInt | TyChar | TyString
          deriving (Ord, Eq)

data Type = Ty Pure Effects          -- ^An impure type `a # e` is respresented as `Ty a e`. A pure type `a` is represented as `Ty a []`
          deriving (Ord, Eq)

data Constraint = Class Name Pure -- TODO: Allow effects and higher kinded types in Classes
                | Sub Type Type
                deriving (Ord, Eq)

-- TODO: Allow quantified effects, e.g., map :: forall a b (e :: Effects). (a -> b # e) -> [a] -> [b] # e
data QPure = Forall [Constraint] [String] Pure deriving (Ord, Eq)

instance Show Effect where
  show (Ef s)    = s
  show (EfUni s) = s

instance Show Prim where
  show TyBool = "Bool"
  show TyInt  = "Int"
  show TyChar = "Char"
  show TyString = "String"

instance Show Constraint where
  show (Sub a b) = show a  ++ " <= " ++ show b
  show (Class c t) = show c ++ " " ++ show t

instance Show Pure where
  show (TyPrim p)    = show p
  show (TyUni s)     = s
  show (TyFun a b)   = parens p (show a) ++ " -> " ++ show b
    where p = case a of (TyFun _ _) -> True
                        _           -> False
  show (TyData s ts) = s ++ unwords (map (\t -> parens (p t) (show t)) ts)
    where p t = case t of (TyFun _ _)  -> True
                          (TyData _ _) -> True
                          _            -> False
  show (TyVar s)     = s

instance Show Type where
  show (Ty p es) = show p ++ (if Set.null es then "" else " # " ++ show es)

instance Show QPure where
  show (Forall cs xs t) = "forall " ++ unwords xs ++ ". " ++ cs' ++ show t
    where cs' = if null cs then "" else "(" ++ unwords  (map show cs) ++ ") => "

parens True  x = "(" ++ x ++ ")"
parens False x = x


subsEffects :: (String -> Maybe Effects) -> Effects -> Effects
subsEffects f m = Set.foldl' Set.union Set.empty (Set.map g m)
                  where g :: Effect -> Set Effect
                        g (Ef s) = Set.singleton (Ef s)
                        g e@(EfUni s) = fromMaybe (Set.singleton e) (f s)

subsType :: (String -> Maybe Pure) -> (String -> Maybe Effects) -> Type -> Type
subsType ft fe (Ty p es) = Ty (subsPure ft fe p) (subsEffects fe es)

subsPure :: (String -> Maybe Pure) -> (String -> Maybe Effects) -> Pure -> Pure
subsPure ft fe = subsPure'
  where subsPure' :: Pure -> Pure
        subsPure' (TyPrim p)    = TyPrim p
        subsPure' t@(TyUni s)   = fromMaybe t (ft s)
        subsPure' (TyFun a b)   = TyFun (subsPure' a) (subsType ft fe b)
        subsPure' (TyData s ts) = TyData s (map subsPure' ts)
        subsPure' t@(TyVar s)   = fromMaybe t (ft s)

subsConstraint :: (String -> Maybe Pure) -> (String -> Maybe Effects) -> Constraint -> Constraint
subsConstraint ft fe = subsC
  where subsC (Class s t) = Class s (subsP t)
        subsC (Sub t1 t2) = Sub (subsT t1) (subsT t2)
        subsP = subsPure ft fe
        subsT = subsType ft fe

shareC :: Pure -> Constraint
shareC = Class "Share"

dropC :: Pure -> Constraint
dropC = Class "Drop"

pureTy :: Pure -> Type
pureTy p = Ty p Set.empty

mono :: Pure -> QPure
mono = Forall [] []
