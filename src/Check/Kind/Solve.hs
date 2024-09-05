{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE ImpredicativeTypes   #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Check.Kind.Solve
  ( run
  ) where

import           Check.Solve
import           Common
import           Introspect
import           Praxis
import           Stage
import           Term

import           Data.List   (nub, sort)
import           Data.Maybe  (fromMaybe)
import           Data.Set    (Set, union)
import qualified Data.Set    as Set


run :: Term a => Annotated a -> Praxis (Annotated a)
run term = do
  term <- solve kindCheckState reduce term
  tryDefault term

reduce :: Disambiguating (Reducer KindConstraint)
reduce disambiguate = \case

  KEq k1 k2 | k1 == k2 -> return tautology

  KEq (_ :< KindUni x) k -> if x `Set.member` kindUnis k then return contradiction else solved (x `is` view value k) -- Note: Occurs check here

  KEq k1 k2@(_ :< KindUni _) -> reduce disambiguate (k2 `KEq` k1) -- handled by the above case

  KEq (_ :< KindFn k1 k2) (_ :< KindFn l1 l2) -> return $ subgoals [ Subgoal (KEq k1 l1), Subgoal (KEq k2 l2) ]

  KPlain (_ :< k) -> case k of
    KindUni _ -> return skip
    KindRef   -> return contradiction
    KindView  -> return contradiction
    _         -> return tautology -- What about Constraint?

  KSub k1 k2 | k1 == k2 -> return tautology

  KSub (_ :< KindUni _) (_ :< KindUni _) -> return skip

  KSub (_ :< KindUni x) (_ :< KindRef) -> solved (x `is` KindRef)

  KSub (_ :< KindUni _) (_ :< KindView) -> return skip

  KSub (_ :< KindRef) (_ :< KindUni _) -> return skip

  KSub (_ :< KindRef) (_ :< KindView) -> return tautology

  KSub (_ :< KindRef) _ -> return contradiction

  KSub (_ :< KindView) (_ :< KindUni x) -> solved (x `is` KindView)

  KSub (_ :< KindView) _ -> return contradiction

  KSub k1 k2 -> return $ subgoals [ Subgoal (KEq k1 k2) ]

  _ -> return contradiction

  where
    kindUnis :: forall a. Term a => Annotated a -> Set Name
    kindUnis = extract (embedMonoid f) where
      f = \case
        KindUni n -> Set.singleton n
        _         -> Set.empty


-- Rewrite helpers
solved :: Resolver -> Praxis (Reduction KindConstraint)
solved resolve = do
  kEnv %%= traverse (pure . sub resolve)
  return (solution (resolve, pure))

is :: Name -> Kind -> Resolver
is n k = embedSub f where
  f (a :< x) = case x of
    KindUni n' -> if n == n' then Just (a :< k) else Nothing
    _          -> Nothing

-- Check for undetermined unification variables, default them where possible
tryDefault :: Term a => Annotated a -> Praxis (Annotated a)
tryDefault term@((src, _) :< _) = do

  -- TODO could just be a warning, and default to Type?
  let freeKinds = deepKindUnis term
  when (not (null freeKinds)) $ throwAt src $ "underdetermined kind: " <> quote (pretty (Set.elemAt 0 freeKinds))
  return term

  where
    deepKindUnis :: forall a. Term a => Annotated a -> Set Name
    deepKindUnis = deepExtract (embedMonoid f) where
      f = \case
        KindUni n -> Set.singleton n
        _         -> Set.empty

