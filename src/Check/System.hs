{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeSynonymInstances  #-}

module Check.System
  ( System
  , initialSystem

  -- |System lenses
  , axioms
  , constraints
  , tySol
  , qTySol
  , kindSol
  , staging
  ) where

import           Check.Constraint (Constraint, Derivation)
import           Common
import           Type             (Kind, Kinded, QType, Type)

import           Control.Lens     (makeLenses)

initialSystem :: System
initialSystem = System
  { _tySol       = []
  , _qTySol      = []
  , _kindSol     = []
  , _constraints = []
  , _axioms      = []
  , _staging     = []
  }

data System = System
  { _tySol       :: [(Name, Kinded Type)]
  , _qTySol      :: [(Name, Kinded QType)]
  , _kindSol     :: [(Name, Kind)]
  , _constraints :: [Derivation]
  , _staging     :: [Derivation]
  , _axioms      :: [Constraint]
  } deriving (Show)

makeLenses ''System

instance PseudoTraversable (Kinded Type) (Kinded Type) System System where
  pseudoTraverse f s =
    tySol (traverse (second f)) s *>
    qTySol (traverse (second (pseudoTraverse f))) s *>
    constraints (traverse (pseudoTraverse f)) s *>
    staging (traverse (pseudoTraverse f)) s *>
    axioms (traverse (pseudoTraverse f)) s

instance PseudoTraversable Kind Kind System System where
  pseudoTraverse f s =
    tySol (traverse (second (pseudoTraverse f))) s *>
    qTySol (traverse (second (pseudoTraverse f))) s *>
    kindSol (traverse (second (pseudoTraverse f))) s *>
    constraints (traverse (pseudoTraverse f)) s *>
    staging (traverse (pseudoTraverse f)) s *>
    axioms (traverse (pseudoTraverse f)) s

instance PseudoTraversable (Kinded QType) (Kinded QType) System System where
  pseudoTraverse f s =
    qTySol (traverse (second f)) s *>
    constraints (traverse (pseudoTraverse f)) s *>
    staging (traverse (pseudoTraverse f)) s *>
    axioms (traverse (pseudoTraverse f)) s

second :: Functor f => (a -> f b) -> (n, a) -> f (n, b)
second f (n, a) = (\b -> (n, b)) <$> f a
