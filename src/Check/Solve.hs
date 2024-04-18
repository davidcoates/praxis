{-# LANGUAGE DeriveFoldable      #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}


module Check.Solve
  ( Rewrite
  , Reduction(..)
  , Reducer(..)
  , solve
  ) where

import           Common
import           Introspect
import           Praxis
import           Print
import           Term

import           Control.Monad (foldM)
import qualified Data.Set      as Set


type Rewrite = forall a. Term a => Annotated a -> Praxis (Annotated a)

data Reduction c = Contradiction | Skip | Solved Rewrite | Subgoals [c] | Tautology

type Reducer c = c -> Praxis (Reduction c)

data Tree c = Branch c [Tree c]
  deriving (Functor, Foldable, Traversable)

data GoalT x c = Goal Source x (Tree c)
  deriving (Functor, Foldable, Traversable)

-- Note: Goal definition is split like this for "deriving" to work.
type Goal c = GoalT (Annotation (Requirement c)) c



solve :: forall c a. (Ord c, Term a, Term c, Term (Requirement c), Pretty (Annotation (Requirement c))) => Lens' PraxisState (System c) -> Reducer c -> Annotated a -> Praxis (Annotated a)
solve system reduce term = do
  requirements' <- use (system . requirements)
  let goals = [ Goal src reason (Branch constraint []) | ((src, Just reason) :< Requirement constraint) <- requirements' ]
  (term, [], _) <- solve' (term, goals)
  return term
  where
    solve' :: (Annotated a, [Goal c]) -> Praxis (Annotated a, [Goal c], Bool)
    solve' (term, []) = return (term, [], undefined)
    solve' (term, goals) = do
      (goals, reduction) <- reduceGoals system reduce (goals)
      case reduction of
        TreeProgress
          -> solve' (term, goals)
        TreeRewrite rewrite
          -> do
            term <- rewrite term
            goals <- traverse (traverse (recurseTerm rewrite)) goals
            -- (system . requirements) %%= traverse (recurse rewrite)
            (system . assumptions) %%= (\as -> Set.fromList <$> (traverse (recurseTerm rewrite) (Set.toList as)))
            solve' (term, goals)
        TreeSkip -- Shouldn't happen...
          -> throw $ "!!! failed to solve constraints !!! " <> separate "\n\n" [ ((src, Just reason) :< Requirement constraint) | Goal src reason (Branch constraint _) <- goals ]


data TreeReduction c = TreeContradiction [c] | TreeProgress | TreeRewrite Rewrite | TreeSkip

noskip :: TreeReduction c -> TreeReduction c
noskip TreeSkip = TreeProgress
noskip r        = r

reduceGoals :: forall c. (Term c, Ord c, Pretty (Annotation (Requirement c))) => Lens' PraxisState (System c) -> Reducer c -> [Goal c] -> Praxis ([Goal c], TreeReduction c)
reduceGoals system reduce [] = return ([], TreeSkip)
reduceGoals system reduce ((Goal src reason tree):goals) = do
  (tree, r1) <- reduceTree system reduce tree
  let
    goal = case tree of
      Just tree -> [Goal src reason tree]
      Nothing   -> []
  case r1 of
    TreeProgress -> do
      (goals, r2) <- reduceGoals system reduce goals
      return (goal ++ goals, noskip r2)
    TreeSkip ->  do
      (goals, r2) <- reduceGoals system reduce goals
      return (goal ++ goals, r2)
    TreeContradiction trace -> throwAt src (printTrace trace)
    _  -> return (goal ++ goals, r1)
  where
    printTrace :: [c] -> Printable String
    printTrace trace = "unable to satisfy constraint" <> "\n  | " <> pretty (last (c:cs)) <> derived <> "\n  | " <> pretty (Style Bold ("hint: " :: Colored String)) <> pretty reason where
      (c:cs) = map ((src, Nothing) :<) trace
      derived = if null cs then blank else pretty (Style Italic (" derived from" :: Colored String)) <> "\n  | " <> pretty c


reduceTree :: forall c. (Ord c, Term c) => Lens' PraxisState (System c) -> Reducer c -> Tree c -> Praxis (Maybe (Tree c), TreeReduction c)
reduceTree system reduce tree@(Branch constraint _) = do

   assumptions' <- use (system . assumptions)
   (tree, r) <- reduceTree' tree
   if constraint `Set.member` assumptions'
     then return (Nothing, TreeProgress)
     else do
       case tree of
         Nothing -> system . assumptions %= (Set.insert constraint)
         _       -> pure ()
       return (tree, r)

  where
    reduceTree' :: Tree c -> Praxis (Maybe (Tree c), TreeReduction c)

    -- leaf case (the constraint has not yet been reduced)
    reduceTree' tree@(Branch constraint []) = do
      r1 <- reduce constraint
      case r1 of
        Contradiction     -> return (Just tree, TreeContradiction [constraint])
        Skip              -> return (Just tree, TreeSkip)
        Solved rewrite    -> return (Nothing, TreeRewrite rewrite)
        Subgoals subgoals -> do
          (tree, r2) <- reduceTree system reduce (Branch constraint (map (\c -> Branch c []) subgoals))
          return (tree, noskip r2)
        Tautology         -> return (Nothing, TreeProgress)

    -- recursive case
    reduceTree' (Branch constraint subtrees) = do
      (subtrees, r1) <- foldM combine ([], TreeSkip) subtrees
      let
        r2 = case r1 of
          TreeContradiction trace -> TreeContradiction (constraint:trace)
          _                       -> r1
      let
        tree = case subtrees of
          [] -> Nothing
          _  -> Just (Branch constraint subtrees)
      return (tree, r2)

    combine :: ([Tree c], TreeReduction c) -> Tree c -> Praxis ([Tree c], TreeReduction c)
    combine (subtrees, r1) subtree = do
      let abort = case r1 of { TreeContradiction _ -> True; TreeRewrite _ -> True; _ -> False }
      if abort
        then return (subtree : subtrees, r1)
        else do
          (subtree, r2) <- reduceTree system reduce subtree
          let
            r3 = case r1 of
              TreeSkip     -> r2
              TreeProgress -> noskip r2
          let
            subtrees' = case subtree of
              Nothing      -> subtrees
              Just subtree -> subtree : subtrees
          return (subtrees', r3)
