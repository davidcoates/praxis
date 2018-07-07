module Vars
  ( Vars(..)
  , generalise
  ) where

import           Effect
import           Record
import           Type

import           Data.Monoid (mconcat)
import           Data.Set    (Set)
import qualified Data.Set    as Set (empty, singleton, toList)

type Names = Set Name

data VarSet = VarSet
  { efVars :: Names
  , efUnis :: Names
  , tyVars :: Names
  , tyUnis :: Names
  }

instance Monoid VarSet where
  mempty = VarSet { efVars = mempty, efUnis = mempty, tyVars = mempty, tyUnis = mempty }
  x `mappend` y = VarSet
    { efVars = efVars x `mappend` efVars y
    , efUnis = efUnis x `mappend` efUnis y
    , tyVars = tyVars x `mappend` tyVars y
    , tyUnis = tyUnis x `mappend` tyUnis y
    }

class Vars a where
  vars :: a -> VarSet
  varsP :: a -> [Name]
  varsP = Set.toList . tyVars . vars
  varsE :: a -> [Name]
  varsE = Set.toList . efVars . vars
  unisP :: a -> [Name]
  unisP = Set.toList . tyUnis . vars
  unisE :: a -> [Name]
  unisE = Set.toList . efUnis . vars

instance Vars Pure where
  vars (TyBang p)    = vars p
  vars (TyData _ ts) = mconcat $ map vars ts
  vars (TyFun t1 t2) = vars t1 `mappend` vars t2
  vars (TyPrim _)    = mempty
  vars (TyRecord r)  = mconcat $ map (vars . snd) (Record.toList r)
  vars (TyUni n)     = mempty{tyUnis = Set.singleton n}
  vars (TyVar v)     = mempty{tyVars = Set.singleton v}

instance Vars Effects where
  vars = mconcat . map vars . Effect.toList

instance Vars Effect where
  vars (EfLit l) = mempty
  vars (EfUni n) = mempty{efUnis = Set.singleton n}
  vars (EfVar v) = mempty{efVars = Set.singleton v}

instance Vars Impure where
  vars (p :# e) = vars p `mappend` vars e

generalise :: Pure -> Type
generalise p = Forall [] (varsP p) (varsE p) p -- TODO Context
