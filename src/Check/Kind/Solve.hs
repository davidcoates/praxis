{-# LANGUAGE ImpredicativeTypes #-}

module Check.Kind.Solve
  ( run
  ) where

import           Check.Solve
import           Check.State
import           Common
import           Introspect
import           Praxis
import           Stage
import           Term

import           Data.List   (nub, sort)
import           Data.Maybe  (fromMaybe)
import           Data.Set    (Set, union)
import qualified Data.Set    as Set


run :: IsTerm a => Annotated KindCheck a -> Praxis (Annotated KindCheck a)
run term = do
  term <- solve (checkState . kindState . kindSolve) reduce term
  tryDefault term

reduce :: Disambiguating (Reducer KindCheck)
reduce disambiguate (a :< constraint) = case constraint of

  KindIsEq kind1 kind2 | kind1 == kind2 -> return tautology

  KindIsEq (_ :< KindUni x) kind -> if x `Set.member` kindUnis kind then return contradiction else solved (x `is` view value kind) -- Note: Occurs check here

  KindIsEq kind1 kind2@(_ :< KindUni _) -> reduce disambiguate (a :< KindIsEq kind2 kind1) -- handled by the above case

  KindIsEq (_ :< KindFn kind1 kind2) (_ :< KindFn kind3 kind4) -> return $ subgoals [ Subgoal (a :< KindIsEq kind1 kind3), Subgoal (a :< KindIsEq kind2 kind4) ]

  KindIsPlain (_ :< kind) -> case kind of
    KindUni _ -> return skip
    KindRef   -> return contradiction
    KindView  -> return contradiction
    _         -> return tautology -- What about Constraint?

  KindIsSub kind1 kind2 | kind1 == kind2 -> return tautology

  KindIsSub (_ :< KindUni _) (_ :< KindUni _) -> return skip

  KindIsSub (_ :< KindUni x) (_ :< KindRef) -> solved (x `is` KindRef)

  KindIsSub (_ :< KindUni _) (_ :< KindView) -> return skip

  KindIsSub (_ :< KindRef) (_ :< KindUni _) -> return skip

  KindIsSub (_ :< KindRef) (_ :< KindView) -> return tautology

  KindIsSub (_ :< KindRef) _ -> return contradiction

  KindIsSub (_ :< KindView) (_ :< KindUni x) -> solved (x `is` KindView)

  KindIsSub (_ :< KindView) _ -> return contradiction

  KindIsSub kind1 kind2 -> return $ subgoals [ Subgoal (a :< KindIsEq kind1 kind2) ]

  _ -> return contradiction

  where
    kindUnis :: forall a. IsTerm a => Annotated KindCheck a -> Set Name
    kindUnis = extract (embedMonoid f) where
      f (_ :< kind)= case kind of
        KindUni n -> Set.singleton n
        _         -> Set.empty


-- Rewrite helpers
solved :: Resolver KindCheck -> Praxis (Reduction KindCheck)
solved resolve = do
  checkState . kindState . typeConEnv %%= traverse (pure . sub resolve)
  checkState . kindState . typeVarEnv %%= traverse (second (pure . sub resolve))
  return (solution (resolve, pure))

is :: Name -> Kind KindCheck -> Resolver KindCheck
is n kind = embedSub f where
  f (a :< x) = case x of
    KindUni n' -> if n == n' then Just (a :< kind) else Nothing
    _          -> Nothing

-- Check for undetermined unification variables, default them where possible
tryDefault :: IsTerm a => Annotated KindCheck a -> Praxis (Annotated KindCheck a)
tryDefault term@((src, _) :< _) = do

  -- TODO could just be a warning, and default to Type?
  let freeKinds = deepKindUnis term
  when (not (null freeKinds)) $ throwAt KindCheck src $ "underdetermined kind: " <> pretty (Set.elemAt 0 freeKinds)
  return term

  where
    deepKindUnis :: forall a. IsTerm a => Annotated KindCheck a -> Set Name
    deepKindUnis = deepExtract (embedMonoid f) where
      f (_ :< kind) = case kind of
        KindUni n -> Set.singleton n
        _         -> Set.empty

