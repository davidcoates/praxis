{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Check.Kind.Solve
  ( run
  ) where

import           Check.Kind.Require
import           Check.Kind.System
import           Check.Solve
import           Common
import           Introspect
import           Praxis
import           Stage
import           Term

import           Data.List          (nub, sort)
import           Data.Maybe         (fromMaybe)
import           Data.Set           (Set, union)
import qualified Data.Set           as Set


run :: Term a => Annotated a -> Praxis (Annotated a)
run term = save stage $ save our $ do
  stage .= KindCheck Solve
  solve (our . constraints) solveKind
  tryDefault term
  simplify term

deepKindUnis :: forall a. Term a => Annotated a -> Set Name
deepKindUnis = deepExtract (embedMonoid f) where
  f = \case
    KindUni n -> Set.singleton n
    _         -> Set.empty

tryDefault :: Term a => Annotated a -> Praxis (Annotated a)
tryDefault term@((src, _) :< _) = do

  kindSol <- use (our . sol)

  -- TODO could just be a warning, and default to Type?
  let freeKinds = deepKindUnis term `Set.difference` Set.fromList (map fst kindSol)
  when (not (null freeKinds)) $ throwAt src $ "underdetermined kind: " <> quote (pretty (Set.elemAt 0 freeKinds))

  return term


kindUnis :: forall a. Term a => Annotated a -> Set Name
kindUnis = extract (embedMonoid f) where
  f = \case
    KindUni n -> Set.singleton n
    _         -> Set.empty

type KindSolver = Solver KindConstraint KindConstraint

solveKind :: KindSolver
solveKind = \case

  KEq k1 k2 | k1 == k2 -> tautology

  KEq (_ :< KindUni x) k -> if x `Set.member` kindUnis k then contradiction else x `is` view value k -- Note: Occurs check here

  KEq k1 k2@(_ :< KindUni _) -> solveKind (k2 `KEq` k1) -- handled by the above case

  KEq (_ :< KindFun s1 s2) (_ :< KindFun t1 t2) -> intro [ KEq s1 t1, KEq s2 t2 ]

  KEq (_ :< KindPair s1 s2) (_ :< KindPair t1 t2) -> intro [ KEq s1 t1, KEq s2 t2 ]

  _ -> contradiction

is :: Name -> Kind -> Praxis (Maybe KindProp)
is n k = do
  our . sol %= ((n, k):)
  simplifyAll
  solved

simplify :: forall a. Term a => Annotated a -> Praxis (Annotated a)
simplify x = do
  kinds <- use (our . sol)
  return $ sub (embedSub (\case { KindUni n -> n `lookup` kinds; _ -> Nothing })) x

simplifyAll :: Praxis ()
simplifyAll = do
  our . sol %%= traverse (second (covalue simplify))
  our . constraints %%= traverse simplify
  kEnv %%= traverse simplify
