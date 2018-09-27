{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}

module Type
  ( Name
  , Type(..)
  , Impure(..)
  , Kinded(..)
  , mono
  , QType(..)
  , TyPat(..)
  , Kind(..)

  , TypeTraversable(..)
  , KindTraversable(..)
  ) where

import           Common
import           Record
import           Tag

import           Control.Applicative   (Const (..))
import           Data.Functor.Identity
import           Data.List             (intercalate)
import           Data.Maybe            (fromMaybe)
import           Data.Monoid           ((<>))
import           Data.Set              (Set)
import qualified Data.Set              as Set

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
deriving instance Ord (TyPat (Tag a))
deriving instance Ord (Type (Tag a))

data QType a = Mono (Type a)
             | Forall [(Name, Kind)] (a (Type a)) (a (Type a)) -- ^First type is constraint

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

instance TagTraversable TyPat where
  tagTraverse' f (TyPatVar n)  = pure $ TyPatVar n
  tagTraverse' f (TyPatPack r) = TyPatPack <$> traverse (tagTraverse f) r


class TypeTraversable a where
  typeTraverse :: Applicative f => (Kinded Type -> f (Kinded Type)) -> a -> f a
  tySub :: (Name -> Maybe (Kinded Type)) -> a -> a
  tySub f = runIdentity . typeTraverse (Identity . f')
      where
        f' (k :< t) = case t of
          TyUni n -> fromMaybe (k :< t) (f n)
          TyVar n -> fromMaybe (k :< t) (f n)
  tySubWithKind :: ((Kind, Name) -> Maybe (Kinded Type)) -> a -> a
  tySubWithKind f = runIdentity . typeTraverse (Identity . f')
      where
        f' (k :< t) = case t of
          TyUni n -> fromMaybe (k :< t) (f (k, n))
          _       -> (k :< t)
  tyUnis :: a -> [Name]
  tyUnis = getConst . typeTraverse (Const . f)
    where
      f (k :< t) = case t of
        TyUni n -> [n]
        _       -> []
  tyVars :: a -> [Name]
  tyVars = getConst . typeTraverse (Const . f)
    where
      f (k :< t) = case t of
        TyVar n -> [n]
        _       -> []

instance (TypeTraversable a, TypeTraversable b) => TypeTraversable (a, b) where
  typeTraverse f (a, b) = (,) <$> typeTraverse f a <*> typeTraverse f b

instance (TypeTraversable a) => TypeTraversable [a] where
  typeTraverse f = sequenceA . fmap (typeTraverse f)

instance (TypeTraversable a) => TypeTraversable (Record a) where
  typeTraverse f = sequenceA . fmap (typeTraverse f)

instance TypeTraversable (Kinded Type) where
  typeTraverse f t@(_ :< TyUni _) = f t
  typeTraverse f t@(_ :< TyVar _) = f t
  typeTraverse f (k :< t) = (k :<) <$> case t of
    (TyApply a b)  -> TyApply <$> typeTraverse f a <*> typeTraverse f b
    (TyBang t)     -> TyBang <$> typeTraverse f t
    (TyCon n)      -> pure $ TyCon n
    (TyEffects es) -> (TyEffects . Set.fromList . concatMap flatten) <$> typeTraverse f (Set.toList es)
      where flatten :: Kinded Type -> [Kinded Type]
            flatten (_ :< TyEffects es) = concatMap flatten es
            flatten t                   = [t]
    (TyLambda a b) -> TyLambda <$> typeTraverse f a <*> typeTraverse f b -- TODO Shadowing?
    (TyPack r)     -> TyPack <$> typeTraverse f r
    (TyRecord r)   -> TyRecord <$> typeTraverse f r

instance TypeTraversable (Kinded TyPat) where
  typeTraverse f = pure

instance TypeTraversable (Kinded b) => TypeTraversable (Kinded (Impure b)) where
  typeTraverse f (k :< t :# e) = (k :<) <$> ((:#) <$> typeTraverse f t <*> typeTraverse f e)

instance TypeTraversable (Kinded QType) where
  typeTraverse f (k :< Mono t) = (\(k :< t) -> k :< Mono t) <$> typeTraverse f (k :< t)
  typeTraverse f (k :< Forall vs cs t) = (\cs t -> k :< Forall vs cs t) <$> typeTraverse f cs <*> typeTraverse f t

class KindTraversable a where
  kindTraverse :: Applicative f => (Kind -> f Kind) -> a -> f a
  kindUnis :: a -> [Name]
  kindUnis = getConst . kindTraverse (Const . f)
    where f (KindUni n) = [n]
          f _           = []
  kindSub :: (Name -> Maybe Kind) -> a -> a
  kindSub f = runIdentity . kindTraverse (Identity . f')
      where f' (KindUni n) = fromMaybe (KindUni n) (f n)
            f' k           = k

instance (KindTraversable a, KindTraversable b) => KindTraversable (a, b) where
  kindTraverse f (a, b) = (,) <$> kindTraverse f a <*> kindTraverse f b

instance (KindTraversable a) => KindTraversable [a] where
  kindTraverse f = sequenceA . fmap (kindTraverse f)

instance (KindTraversable a) => KindTraversable (Record a) where
  kindTraverse f = sequenceA . fmap (kindTraverse f)

instance KindTraversable (Kinded Type) where
  kindTraverse = tagTraverse

instance TagTraversable b => KindTraversable (Kinded (Impure b)) where
  kindTraverse = tagTraverse

instance KindTraversable (Kinded QType) where
  kindTraverse f k = case k of
    (k :< Mono t)         -> (\(k :< t) -> k :< Mono t) <$> kindTraverse f (k :< t)
    (k :< Forall vs cs t) -> (:<) <$> kindTraverse f k <*> ((\cs t -> Forall vs cs t) <$> kindTraverse f cs <*> kindTraverse f t)

instance KindTraversable Kind where
  kindTraverse f k = case k of
    KindUni _     -> f k
    KindFun k1 k2 -> KindFun <$> kindTraverse f k1 <*> kindTraverse f k2
    KindRecord r  -> KindRecord <$> kindTraverse f r
    _             -> pure k
