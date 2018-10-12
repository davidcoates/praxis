{-# LANGUAGE StandaloneDeriving #-}

module Type
  ( Kind(..)
  , Name
  , QType(..)
  , TyPat(..)
  , Type(..)

--  , Polymorphic(..)
  ) where

import           Annotate
import           Common
import           Record

import           Data.List   (intercalate)
import           Data.Maybe  (fromMaybe)
import           Data.Monoid ((<>))
import           Data.Set    (Set)
import qualified Data.Set    as Set

data Kind = KindUni Name
          | KindConstraint
          | KindEffect
          | KindFun Kind Kind
          | KindRecord (Record Kind)
          | KindType
  deriving (Ord, Eq)

data QType a = Mono (Annotated a Type)
             | Forall [(Name, Kind)] (Annotated a Type) (Annotated a Type) -- ^First type is constraint
             | QTyUni Name

data Type a = TyUni Name                                      -- Compares less than all other types
            | TyApply (Annotated a Type) (Annotated a Type)   -- ^Type-level application : (a -> #b) -> #a -> #b
            | TyBang (Annotated a Type)
            | TyCon Name                                      -- ^Includes (->) : [T, T , E] -> T
            | TyFlat (Set (Annotated a Type))                 -- Used for effects and constraints
            | TyLambda (Annotated a TyPat) (Annotated a Type) -- ^A type-level lambda : ?1 -> ?2
            | TyPack   (Record (Annotated a Type))            -- ^A type pack with a record kind
            | TyRecord (Record (Annotated a Type))            -- ^A type record : T
            | TyVar Name                                      -- ^A type variable

data TyPat a = TyPatVar Name
             | TyPatPack (Record (Annotated a TyPat))

deriving instance Eq (TyPat a)
deriving instance Eq (Type a)
deriving instance Eq (QType a)
deriving instance Ord (TyPat a)
deriving instance Ord (Type a)
deriving instance Ord (QType a)

{-
-- TODO precedence and so on
instance (Show (Annotation a Type), Annotated a Type ~ b) => Show (Type a) where
  show t = case t of
    TyApply (_ :< TyCon "->") (_ :< TyPack r) | [a, b] <- map snd $ Record.toList r -> "(" ++ show_ a ++ " -> " ++ show_ b ++ ")"
    TyApply a b   -> show_ a ++ " " ++ show_ b
    TyBang t      -> "!" ++ show_ t
    TyCon n       -> n
    TyFlat ts     -> "{" ++ intercalate ", " (map show_ (Set.toList ts)) ++ "}"
    TyLambda a b  -> "\\" ++ show_ a ++ " -> " ++ show_ b
    TyPack r      -> "[" ++ Record.showGuts show_ r ++ "]"
    TyRecord r    -> "(" ++ Record.showGuts show_ r ++ ")"
    TyUni n       -> n
    TyVar v       -> v
-}
{-
instance (Show (Annotated a b), Show (Annotated a Type), Annotated a (Impure b) ~ c) => Show c where
  show (a :< t :# es) = show t ++ " # " ++ show es -- TODO hide annotation from t

instance (Show (Annotation a QType), Show (Annotated a Type)) => Show (Annotated a QType) where
  show (a :< q) = case q of
    Mono t               -> show t
    Forall vs c (_ :< t) -> "forall " ++ unwords (map fst vs) ++  ". " ++ (show c ++ " => ") ++ show (a :< t) -- TODO this isn't quite right
    QTyUni n             -> n ++ " @ " ++ show a

instance Show (Annotation a TyPat) => Show (Annotated a TyPat) where
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

instance AnnTraversable Type where
  annTraverse' f t = case t of
    TyApply a b  -> TyApply <$> annTraverse f a <*> annTraverse f b
    TyBang t     -> TyBang <$> annTraverse f t
    TyCon n      -> pure $ TyCon n
    TyFlat ts    -> TyFlat . Set.fromList <$> traverse (annTraverse f) (Set.toList ts)
    TyLambda a b -> TyLambda <$> annTraverse f a <*> annTraverse f b
    TyPack r     -> TyPack <$> traverse (annTraverse f) r
    TyRecord r   -> TyRecord <$> traverse (annTraverse f) r
    TyUni n      -> pure $ TyUni n
    TyVar v      -> pure $ TyVar v

instance AnnTraversable b => AnnTraversable (Impure b) where
  annTraverse' f (t :# e) = (:#) <$> annTraverse f t <*> annTraverse f e

instance AnnTraversable QType where
  annTraverse' f (Mono t)        = Mono <$> annTraverse f t
  annTraverse' f (Forall vs c t) = Forall vs <$> annTraverse f c <*> annTraverse f t
  annTraverse' f (QTyUni n)      = pure (QTyUni n)

instance AnnTraversable TyPat where
  annTraverse' f (TyPatVar n)  = pure $ TyPatVar n
  annTraverse' f (TyPatPack r) = TyPatPack <$> traverse (annTraverse f) r


class Polymorphic a where
  unis :: a -> [Name]
  vars :: a -> [Name]
-}

{-

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
  pseudoTraverse = annTraverse

instance PseudoTraversable Kind Kind (Kinded QType) (Kinded QType) where
  pseudoTraverse f k = case k of
    (k :< Mono t)         -> (\(k :< t) -> k :< Mono t) <$> pseudoTraverse f (k :< t)
    (k :< Forall vs cs t) -> (:<) <$> pseudoTraverse f k <*> ((\cs t -> Forall vs cs t) <$> pseudoTraverse f cs <*> pseudoTraverse f t)
    (k :< QTyUni n)       -> (:<) <$> pseudoTraverse f k <*> pure (QTyUni n)

-}
