module Type
  ( Name
  , Kind(..)
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
  , share
  , mono
  , empty
  , unions
  , singleton
  ) where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)
import Common
import Record

-- TODO need more kinds? KindRecord?
data Kind = KindEffects     -- 
          | KindPure        -- 
          | KindImpure      -- Do we need this? This is basically (KindPure, KindEffects)
          | KindConstraint  -- 
          | KindRecord (Record Kind)

{-
data XType = XTyEffects Effects
           | XTyPure Pure
           | XTyImpure Type -- TODO do we need this? -- TODO Rename Type to Impure? type Type = Pure ?
           | XTyConstraint Constraint
           | XTyLambda Name IType -- TODO
           | XTyRecord (Record IType)

data XKind = XKindBase Kind
           | XKindLambda Kind XKind -- TODO Kind Pure ?
           | XKindRecord (Record XKind)
-}

{-|
  Effects functions as a *flat set* of effect.
  An effect unification variable can be replaced with a flat set of effects, e.g.,
  { EfUni α, EfLit "Read IO" } if α ~> { EfLit "WriteIO", EfLit "ReadHeap" } then the result is { EfLit "WriteIO", EfLit "ReadHeap", EfLit "Read IO" }
-}
data Effect = EfLit String           -- ^A concrete effect e.g., Eg `ReadIO`
            | EfVar String           -- ^An effect variable (e.g., e in forall a b e. (a -> b # e) -> [a] -> [b] # e)
            | EfUni String           -- ^An effect unification variable
            deriving (Ord, Eq)

type Effects = Set Effect

empty :: Effects
empty = Set.empty

unions :: [Effects] -> Effects
unions = Set.unions

singleton :: Effect -> Effects
singleton = Set.singleton

-- |A *top-level* pure type
data Pure = TyPrim Prim              -- ^A primitive type -- TODO get rid of this eventually
          | TyRecord (Record Pure)   -- ^A record type
          | TyUni String             -- ^A (pure) type unification variable
          | TyFun Pure Type          -- ^A function `a -> b # e` is represented as TyFun a (TyImpure b e)
          | TyData String [Pure]     -- ^A fully-applied datatype e.g., TyData "Pair" [TyPrim Int, TyPrim Bool] -- TODO not [Pure], but XPure?
          | TyVar String             -- ^A type variable (e.g., a in forall a. a -> a)
          | TyBang Pure              -- ^A read-only reference
          deriving (Ord, Eq)

-- Perhaps ultimately replace this with TyData "Bool" [], TyData "Int" []
data Prim = TyBool | TyInt | TyChar | TyString
          deriving (Ord, Eq)

-- TODO deep annotations?
data Type = Pure :# Effects
          deriving (Ord, Eq)

data Constraint = Class Name Pure -- TODO: Allow effects and higher kinded types in Classes
                | EqualP Pure Pure
                | EqualE Effects Effects
                -- TODO need EqualK at least internally?
                deriving (Ord, Eq)

-- TODO: Allow quantified effects, e.g., map :: forall a b (e :: Effects). (a -> b # e) -> [a] -> [b] # e
data QPure = Forall [Constraint] [String] Pure deriving (Ord, Eq)

instance Show Kind where
  show KindEffects    = "E"
  show KindPure       = "P"
  show KindImpure     = "I"
  show KindConstraint = "C"
  show (KindRecord r) = show r

instance Show Effect where
  show (EfLit s) = s
  show (EfUni s) = s
  show (EfVar s) = s

instance Show Prim where
  show TyBool = "Bool"
  show TyInt  = "Int"
  show TyChar = "Char"
  show TyString = "String"

instance Show Constraint where
  show (EqualP a b) = show a  ++ " ~ " ++ show b
  show (EqualE a b) = show a  ++ " ~ " ++ show b
  show (Class c t)  = show c ++ " " ++ show t

instance Show Pure where
  show (TyPrim p)    = show p
  show (TyRecord r)  = show r
  show (TyUni s)     = s
  show (TyFun a b)   = parens p (show a) ++ " -> " ++ show b
    where p = case a of (TyFun _ _) -> True
                        _           -> False
  show (TyData s ts) = s ++ unwords (map (\t -> parens (p t) (show t)) ts)
    where p t = case t of (TyFun _ _)  -> True
                          (TyData _ _) -> True
                          _            -> False
  show (TyVar s)     = s

  show (TyBang p)    = "bang(" ++ show p ++ ")"

instance Show Type where
  show (p :# es) = show p ++ (if Set.null es then "" else " # " ++ show es)

instance Show QPure where
  show (Forall cs xs t) = "forall " ++ unwords xs ++ ". " ++ cs' ++ show t
    where cs' = if null cs then "" else "(" ++ unwords  (map show cs) ++ ") => "

parens True  x = "(" ++ x ++ ")"
parens False x = x


subsEffects :: (String -> Maybe Effects) -> Effects -> Effects
subsEffects f m = Set.foldl' Set.union Set.empty (Set.map g m)
                  where g :: Effect -> Set Effect
                        g e@(EfUni s) = fromMaybe (singleton e) (f s)
                        g e           = singleton e

subsType :: (String -> Maybe Pure) -> (String -> Maybe Effects) -> Type -> Type
subsType ft fe (p :# es) = subsPure ft fe p :# subsEffects fe es

subsPure :: (String -> Maybe Pure) -> (String -> Maybe Effects) -> Pure -> Pure
subsPure ft fe = subsPure'
  where subsPure' :: Pure -> Pure
        subsPure' (TyRecord r)  = TyRecord (fmap subsPure' r)
        subsPure' (TyPrim p)    = TyPrim p
        subsPure' t@(TyUni s)   = fromMaybe t (ft s)
        subsPure' (TyFun a b)   = TyFun (subsPure' a) (subsType ft fe b)
        subsPure' (TyData s ts) = TyData s (map subsPure' ts)
        subsPure' t@(TyVar s)   = fromMaybe t (ft s)

subsConstraint :: (String -> Maybe Pure) -> (String -> Maybe Effects) -> Constraint -> Constraint
subsConstraint ft fe = subsC
  where subsC (Class s t) = Class s (subsP t)
        subsC (EqualP p1 p2) = EqualP (subsP p1) (subsP p2)
        subsC (EqualE e1 e2) = EqualE (subsE e1) (subsE e2)
        subsP = subsPure ft fe
        subsE = subsEffects fe

share :: Pure -> Constraint
share = Class "Share"

mono :: Pure -> QPure
mono = Forall [] []
