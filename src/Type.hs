{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Type
  ( Name
  , Kind(..)
  , Effect(..)
  , Effects(..)
  , Pure(..)
  , Prim(..)
  , Impure(..)
  , Constraint(..)
  , Type(..)
  , Term(..)
  , Sub(..)
  , share
  , empty
  , unions
  , singleton
  ) where

import           Common
import           Data.Maybe (fromMaybe)
import           Data.Set   (Set, elems)
import qualified Data.Set   as Set
import           Record

import           Data.List  (intercalate)

-- TODO need more kinds? KindRecord?
data Kind = KindConstraint  --
          | KindEffects     --
          | KindImpure      -- Do we need this? This is basically (KindPure, KindEffects)
          | KindPure        --
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
            | EfUni String           -- ^An effect unification variable
            | EfVar String           -- ^An effect variable (e.g., e in forall a b e. (a -> b # e) -> [a] -> [b] # e)
            deriving (Ord, Eq)

newtype Effects = Effects { getEffects :: Set Effect }
  deriving (Ord, Eq)

instance Show Effects where
  show (Effects es) = "{" ++ intercalate ", " (map show (elems es)) ++ "}"

empty :: Effects
empty = Effects Set.empty

unions :: [Effects] -> Effects
unions = Effects . Set.unions . map getEffects

singleton :: Effect -> Effects
singleton = Effects . Set.singleton

-- |A *top-level* pure type
data Pure = TyBang Pure              -- ^A read-only reference
          | TyData String [Pure]     -- ^A fully-applied datatype e.g., TyData "Pair" [TyPrim Int, TyPrim Bool] -- TODO not [Pure], but XPure?
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
                | EqualE Effects Effects
                | EqualP Pure Pure
                -- TODO need EqualK at least internally?
                deriving (Ord, Eq)

-- TODO: Allow quantified effects, e.g., map :: forall a b (e :: Effects). (a -> b # e) -> [a] -> [b] # e
data Type = Mono Impure
          | Forall [Constraint] [Name] Pure
  deriving (Ord, Eq)

instance Show Kind where
  show KindConstraint = "C"
  show KindEffects    = "E"
  show KindImpure     = "I"
  show KindPure       = "P"
  show (KindRecord r) = show r

instance Show Effect where
  show (EfLit s) = s
  show (EfUni s) = s
  show (EfVar s) = s

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
  show (Forall cs xs t) = "forall " ++ unwords xs ++ ". " ++ cs' ++ show t
    where cs' = if null cs then "" else "(" ++ unwords  (map show cs) ++ ") => "

parens True  x = "(" ++ x ++ ")"
parens False x = x


share :: Pure -> Constraint
share = Class "Share"

data Term = TermPure Pure
          | TermEffects Effects
  deriving (Ord, Eq)

instance Show Term where
  show (TermPure p)    = show p
  show (TermEffects e) = show e

class Sub a where
  sub :: (Name -> Maybe Term) -> a -> a

  subP :: (Name -> Maybe Pure) -> a -> a
  subP f = sub (\n -> TermPure <$> f n)
  subE :: (Name -> Maybe Effects) -> a -> a
  subE f = sub (\n -> TermEffects <$> f n)

instance Sub Pure where
  sub f (TyBang    p) = sub f p
  sub f (TyData i ps) = TyData i (map (sub f) ps)
  sub f (TyFun p1 t2) = TyFun (sub f p1) (sub f t2)
  sub f (TyPrim p)    = TyPrim p
  sub f (TyRecord r)  = TyRecord (fmap (sub f) r)
  sub f t             = case t of
    TyUni n -> g (TyUni n) n
    TyVar n -> g (TyVar n) n
    where g t n | Just (TermPure p) <- f n = p
                | Nothing           <- f n = t
                | otherwise                = error "Bad term substitution"

instance Sub Impure where
  sub f (p :# e) = sub f p :# sub f e

instance Sub Constraint where
  sub f (Class c p)    = Class c (sub f p)
  sub f (EqualE e1 e2) = EqualE (sub f e1) (sub f e2)
  sub f (EqualP p1 p2) = EqualP (sub f p1) (sub f p2)

instance Sub Type where
  sub f (Mono t) = Mono (sub f t)
  sub f t        = t

instance Sub Effects where
  sub f (Effects es) = Effects $ Set.foldl' Set.union Set.empty (Set.map h es)
    where h (EfUni n) = g (EfUni n) n
          h (EfVar n) = g (EfVar n) n
          h e         = Set.singleton e
          g :: Effect -> Name -> Set Effect
          g e n | Just (TermEffects e) <- f n = getEffects e
                | Nothing              <- f n = Set.singleton e
                | otherwise                   = error "Bad term substitution"

instance Sub Term where
  sub f (TermPure p)    = TermPure $ sub f p
  sub f (TermEffects e) = TermEffects $ sub f e

instance Sub a => Sub [a] where
  sub f = map (sub f)
