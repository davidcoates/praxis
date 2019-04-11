{-# LANGUAGE StandaloneDeriving #-}

module Type
  ( Kind(..)
  , Name
  , QType(..)
  , TyPat(..)
  , Type(..)

--  , Polymorphic(..)
  ) where

import           Common
import           Record

import           Data.List   (intercalate)
import           Data.Maybe  (fromMaybe)
import           Data.Monoid ((<>))
import           Data.Set    (Set)
import qualified Data.Set    as Set

data Kind = KindUni Name
          | KindConstraint
          | KindFun Kind Kind
          | KindRecord (Record Kind)
          | KindType
  deriving (Ord, Eq)

data QType a = Mono (Annotated a Type)
             | Forall [(Name, Kind)] (Annotated a Type) (Annotated a Type) -- ^First type is constraint

data Type a = TyUni Name                                      -- Compares less than all other types
            | TyApply (Annotated a Type) (Annotated a Type)   -- ^Type-level application : (#a -> #b) -> #a -> #b
            | TyBang (Annotated a Type)
            | TyCon Name                                      -- ^Includes (->) : [T, T] -> T
            | TyFlat (Set (Annotated a Type))                 -- Used for constraints
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

instance Show Kind where
  show k = case k of
    KindUni n      -> n
    KindConstraint -> "Constraint"
    KindFun k1 k2  -> show k1 ++ " -> " ++ show k2
    KindRecord r   -> "[" ++ showGuts show r ++ "]"
    KindType       -> "Type"
