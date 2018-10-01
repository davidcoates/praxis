{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving    #-}

module Type
  ( Name
  , Type(..)
  , Impure(..)
  , Kinded(..)
  , mono
  , QType(..)
  , TyPat(..)
  , Kind(..)

  , TypeTraversable
  , KindTraversable
  , Polymorphic(..)
  ) where

import           Common
import           Record
import           Tag

import           Data.List   (intercalate)
import           Data.Maybe  (fromMaybe)
import           Data.Monoid ((<>))
import           Data.Set    (Set)
import qualified Data.Set    as Set

data Type a = TyUni Name -- Compares less than all other types
            | TyApply (a (Type a)) (a (Type a))   -- ^Type-level application : (a -> #b) -> #a -> #b
            | TyBang (a (Type a))
            | TyCon Name                          -- ^Includes (->) : [T, T , E] -> T
            | TyEffects (Set (a (Type a)))        -- TODO perhaps call TyEffects TyFlat, use for constraints also
            | TyLambda (a (TyPat a)) (a (Type a)) -- ^A type-level lambda : ?1 -> ?2
            | TyPack   (Record (a (Type a)))      -- ^A type pack with a record kind
            | TyRecord (Record (a (Type a)))      -- ^A type record : T
            | TyVar Name                          -- ^A type variable

data Impure b a = (a (b a)) :# (a (Type a))

type Kinded a = Tagged Kind a

deriving instance Eq (TyPat (Tag a))
deriving instance Eq (Type (Tag a))
deriving instance Eq (QType (Tag a))
deriving instance Ord (TyPat (Tag a))
deriving instance Ord (Type (Tag a))
deriving instance Ord (QType (Tag a))

data QType a = Mono (Type a)
             | Forall [(Name, Kind)] (a (Type a)) (a (Type a)) -- ^First type is constraint
             | QTyUni Name

mono :: Tagged a Type -> Tagged a QType
mono (a :< t) = a :< Mono t

data TyPat a = TyPatVar Name
             | TyPatPack (Record (a (TyPat a)))

data Kind = KindUni Name -- Compares less than all other kinds
          | KindConstraint
          | KindEffect
          | KindFun Kind Kind
          | KindRecord (Record Kind)
          | KindType
  deriving (Ord, Eq)

-- TODO precedence and so on
instance Show a => Show (Tagged a Type) where
  show (a :< t) = show' (a :< t) ++ " @ " ++ show a where
    show' (_ :< t) = case t of
      TyApply (_ :< TyCon "->") (_ :< TyPack r) | [a, b] <- map snd $ Record.toList r -> "(" ++ show' a ++ " -> " ++ show' b ++ ")"
      TyApply a b   -> show' a ++ " " ++ show' b
      TyBang t      -> "!" ++ show' t
      TyCon n       -> n
      TyEffects es  -> "{" ++ intercalate ", " (map show' (Set.toList es)) ++ "}"
      TyLambda a b  -> "\\" ++ show a ++ " -> " ++ show' b
      TyPack r      -> "[" ++ Record.showGuts show' r ++ "]"
      TyRecord r    -> "(" ++ Record.showGuts show' r ++ ")"
      TyUni n       -> n
      TyVar v       -> v

instance (Show a, Show (Tagged a b)) => Show (Tagged a (Impure b)) where
  show (a :< t :# es) = show t ++ " # " ++ show es -- TODO hide annotation from t

instance Show a => Show (Tagged a QType) where
  show (a :< Mono t) = show (a :< t)
  show (a :< Forall vs c (_ :< t)) = "forall " ++ unwords (map fst vs) ++  ". " ++ (show c ++ " => ") ++ show (a :< t) -- TODO this isn't quite right
  show (a :< QTyUni n) = n

instance Show a => Show (Tagged a TyPat) where
  show (_ :< TyPatVar n)  = n
  show (_ :< TyPatPack r) = "[" ++ Record.showGuts show r ++ "]"

instance Show Kind where
  show KindConstraint = "Constraint"
  show KindEffect     = "Effect"
  show (KindFun a b)  | KindFun _ _ <- a = "(" ++ show a ++ ") -> " ++ show b
                      | otherwise        = show a ++ " -> " ++ show b
  show (KindRecord r) = "[" ++ Record.showGuts show r ++ "]"
  show KindType       = "Type"
  show (KindUni n)    = n

instance TagTraversable Type where
  tagTraverse' f t = case t of
    TyApply a b  -> TyApply <$> tagTraverse f a <*> tagTraverse f b
    TyBang t     -> TyBang <$> tagTraverse f t
    TyCon n      -> pure $ TyCon n
    TyEffects es -> TyEffects . Set.fromList <$> traverse (tagTraverse f) (Set.toList es)
    TyLambda a b -> TyLambda <$> tagTraverse f a <*> tagTraverse f b
    TyPack r     -> TyPack <$> traverse (tagTraverse f) r
    TyRecord r   -> TyRecord <$> traverse (tagTraverse f) r
    TyUni n      -> pure $ TyUni n
    TyVar v      -> pure $ TyVar v

instance TagTraversable b => TagTraversable (Impure b) where
  tagTraverse' f (t :# e) = (:#) <$> tagTraverse f t <*> tagTraverse f e

instance TagTraversable QType where
  tagTraverse' f (Mono t)        = Mono <$> tagTraverse' f t
  tagTraverse' f (Forall vs c t) = (\c t -> Forall vs c t) <$> tagTraverse f c <*> tagTraverse f t
  tagTraverse' f (QTyUni n)      = pure (QTyUni n)

instance TagTraversable TyPat where
  tagTraverse' f (TyPatVar n)  = pure $ TyPatVar n
  tagTraverse' f (TyPatPack r) = TyPatPack <$> traverse (tagTraverse f) r


class Polymorphic a where
  unis :: a -> [Name]
  vars :: a -> [Name]

type TypeTraversable a = SemiTraversable (Kinded Type) a

instance Polymorphic (Kinded Type) where
  unis t@(_ :< t') = case t' of
    TyUni n -> [n]
    _       -> []
  vars t@(_ :< t') = case t' of
    TyVar n -> [n]
    _       -> []

instance Polymorphic (Kinded QType) where
  unis t@(_ :< QTyUni n) = [n]
  unis _                 = []
  vars _ = []

instance Polymorphic Kind where
  unis (KindUni n) = [n]
  unis _           = []
  vars k = []

instance Substitutable Name (Kinded Type) where
  sub f t@(_ :< t') = case t' of
    TyUni n -> fromMaybe t (f n)
    TyVar n -> fromMaybe t (f n)
    _       -> t

instance Substitutable (Kind, Name) (Kinded Type) where
  sub f t@(k :< t') = case t' of
    TyUni n -> fromMaybe t (f (k, n))
    TyVar n -> fromMaybe t (f (k, n))
    _       -> t

instance Substitutable Name (Kinded QType) where
  sub f t@(_ :< t') = case t' of
    QTyUni n -> fromMaybe t (f n)
    _        -> t

instance Substitutable Name Kind where
  sub f k = case k of
    KindUni n -> fromMaybe k (f n)
    _         -> k

instance PseudoTraversable (Kinded Type) (Kinded Type) (Kinded Type) (Kinded Type) where
  pseudoTraverse f t@(_ :< TyUni _) = f t
  pseudoTraverse f t@(_ :< TyVar _) = f t
  pseudoTraverse f (k :< t) = (k :<) <$> case t of
    TyApply a b  -> TyApply <$> pseudoTraverse f a <*> pseudoTraverse f b
    TyBang t     -> TyBang <$> pseudoTraverse f t
    TyCon n      -> pure $ TyCon n
    TyEffects es -> (TyEffects . Set.fromList . concatMap flatten) <$> traverse (pseudoTraverse f) (Set.toList es)
      where flatten :: Kinded Type -> [Kinded Type]
            flatten (_ :< TyEffects es) = concatMap flatten es
            flatten t                   = [t]
    TyLambda a b -> TyLambda <$> pseudoTraverse f a <*> pseudoTraverse f b -- TODO Shadowing?
    TyPack r     -> TyPack <$> traverse (pseudoTraverse f) r
    TyRecord r   -> TyRecord <$> traverse (pseudoTraverse f) r

instance PseudoTraversable (Kinded Type) (Kinded Type) (Kinded TyPat) (Kinded TyPat) where
  pseudoTraverse f = pure

instance PseudoTraversable (Kinded Type) (Kinded Type) (Kinded QType) (Kinded QType) where
  pseudoTraverse f (k :< Mono t) = (\(k :< t) -> k :< Mono t) <$> pseudoTraverse f (k :< t)
  pseudoTraverse f (k :< Forall vs cs t) = (\cs t -> k :< Forall vs cs t) <$> pseudoTraverse f cs <*> pseudoTraverse f t
  pseudoTraverse f t@(_ :< QTyUni _) = pure t

instance PseudoTraversable (Kinded QType) (Kinded QType) (Kinded QType) (Kinded QType) where
  pseudoTraverse f t@(_ :< QTyUni _) = f t
  pseudoTraverse f t                 = pure t

type KindTraversable a = SemiTraversable Kind a

instance PseudoTraversable Kind Kind Kind Kind where
  pseudoTraverse f k = case k of
    KindUni _     -> f k
    KindFun k1 k2 -> KindFun <$> pseudoTraverse f k1 <*> pseudoTraverse f k2
    KindRecord r  -> KindRecord <$> traverse (pseudoTraverse f) r
    _             -> pure k

instance PseudoTraversable Kind Kind (Kinded Type) (Kinded Type) where
  pseudoTraverse = tagTraverse

instance PseudoTraversable Kind Kind (Kinded QType) (Kinded QType) where
  pseudoTraverse f k = case k of
    (k :< Mono t)         -> (\(k :< t) -> k :< Mono t) <$> pseudoTraverse f (k :< t)
    (k :< Forall vs cs t) -> (:<) <$> pseudoTraverse f k <*> ((\cs t -> Forall vs cs t) <$> pseudoTraverse f cs <*> pseudoTraverse f t)
    (k :< QTyUni n)       -> (:<) <$> pseudoTraverse f k <*> pure (QTyUni n)
