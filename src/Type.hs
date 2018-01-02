module Type
  ( Effect(..)
  , Effects
  , Pure(..)
  , Prim(..)
  , Type(..)
  , Constraint(..)
  , QType(..)
  , subsEffects
  , subsType
  , pureType
  ) where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (intercalate)
import Data.Maybe (fromMaybe)

{-
  Effects functions as a *flat set* of effect.
  An effect unification variable can be replaced with a flat set of effects, e.g.,
  { EfUni α, EfString "Read IO" } if α ~> { Ef "WriteIO", Ef "ReadHeap" } then the result is { Ef "WriteIO", Ef "ReadHeap", Ef "Read IO" }
-}
data Effect = Ef String              -- A concrete effect e.g., Eg `ReadIO`
            | EfUni String           -- An effect unification variable
            deriving (Ord, Eq)

type Effects = Set Effect

-- A *top-level* pure type
data Pure = TyPrim Prim              -- A primitive type
          | TyUni String             -- A (pure) type unification variable
          | TyFun Pure Type          -- `a -> b # e` is represented as TyFun a (TyImpure b e)
          | TyData String [Pure]     -- A fully-applied datatype e.g., TyData "Pair" [TyPrim Int, TyPrim Bool]
          | TyVar String             -- A type variable (e.g., a in forall a. a -> a)
          deriving (Ord, Eq)

-- Perhaps ultiamtely replace this with TyData "Bool" [], TyData "Int" []
data Prim = TyBool | TyInt
          deriving (Ord, Eq)

data Type = Ty Pure Effects          -- `a # e` is respresented as `Ty a e`. A pure type `a` is represented as `Ty a []`
          deriving (Ord, Eq)

pureType :: Pure -> Type
pureType p = Ty p Set.empty

-- TODO: Allow multi-parameter type classes
data Constraint = Constraint String Type

-- TODO: Allow quantified effects, e.g., map :: forall a b (e :: Effects). (a -> b # e) -> [a] -> [b] # e
data QType = Forall [Constraint] [String] Type


instance Show Effect where
  show (Ef s)    = s
  show (EfUni s) = s

instance Show Prim where
  show TyBool = "Bool"
  show TyInt  = "Int"

parens True  x = "(" ++ x ++ ")"
parens False x = x

instance Show Pure where
  show (TyPrim p)    = show p
  show (TyUni s)     = s
  show (TyFun a b)   = parens p (show a) ++ " -> " ++ show b
    where p = case a of (TyFun _ _) -> True
                        _           -> False
  show (TyData s ts) = s ++ intercalate " " (map (\t -> parens (p t) (show t)) ts)
    where p t = case t of (TyFun _ _)  -> True
                          (TyData _ _) -> True
                          _            -> False
  show (TyVar s)     = s

instance Show Type where
  show (Ty p es) = show p ++ (if Set.null es then "" else " # " ++ show es)

instance Show Constraint where
  show (Constraint s t) = s ++ " (" ++ show t ++ ")"

instance Show QType where
  show (Forall cs xs t) = "forall " ++ intercalate " " xs ++ ". " ++ cs' ++ show t
    where cs' = if null cs then "" else "(" ++ intercalate " "  (map show cs) ++ ") => "


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
