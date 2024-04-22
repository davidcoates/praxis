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
  term <- solve kindSystem reduce term
  tryDefault term

reduce :: Reducer KindConstraint
reduce = \case

  KEq k1 k2 | k1 == k2 -> return Tautology

  KEq (_ :< KindUni x) k -> if x `Set.member` kindUnis k then return Contradiction else solved (x `is` view value k) -- Note: Occurs check here

  KEq k1 k2@(_ :< KindUni _) -> reduce (k2 `KEq` k1) -- handled by the above case

  KEq (_ :< KindFun k1 k2) (_ :< KindFun l1 l2) -> return $ Subgoals [ KEq k1 l1, KEq k2 l2 ]

  KEq (_ :< KindPair k1 k2) (_ :< KindPair l1 l2) -> return $ Subgoals [ KEq k1 l1, KEq k2 l2 ]

  KSub k1 k2 | k1 == k2 -> return Tautology

  KSub (_ :< KindUni x) (_ :< KindType) -> solved (x `is` KindType)

  KSub (_ :< KindType) (_ :< KindUni x) -> solved (x `is` KindType)

  KSub (_ :< KindPair k1 k2) (_ :< KindPair l1 l2) -> return $ Subgoals [ KSub k1 l1, KSub k2 l2 ]

  KSub (_ :< KindView d1) (_ :< KindView d2)
    | d1 <= d2  -> return Tautology
    | otherwise -> return Contradiction

  KSub (_ :< KindUni _) _ -> return Skip

  KSub _ (_ :< KindUni _) -> return Skip

  _ -> return Contradiction

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
  return (Solved (resolve, pure))

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

