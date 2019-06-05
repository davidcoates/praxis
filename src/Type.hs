module Type
  ( QType(..)
  , TyPat(..)
  , Type(..)
  , Constraint(..)
  ) where

import           Common
import           Kind     (Kind)
import           Record

import           Data.Set (Set)

data QType a = Mono (Annotated a Type)
             | Forall [Name] (Annotated a Type)
  deriving (Eq, Ord)

data TyPat a = TyPatVar Name
             | TyPatPack (Record (Annotated a TyPat))
  deriving (Eq, Ord)

data Type a = TyUni Name                                      -- Compares less than all other types
            | TyApply (Annotated a Type) (Annotated a Type)
            | TyBang (Annotated a Type)
            | TyCon Name
            | TyFlat (Set (Annotated a Type))                 -- Used for constraints
            | TyFun (Annotated a Type) (Annotated a Type)
            | TyPack   (Record (Annotated a Type))            -- ^A type pack with a record kind
            | TyRecord (Record (Annotated a Type))            -- ^A type record : T
            | TyVar Name
  deriving (Eq, Ord)

data Constraint a = Class (Annotated a Type)
                  | Eq (Annotated a Type) (Annotated a Type)
  deriving (Eq, Ord)
