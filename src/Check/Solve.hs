{-# LANGUAGE DeriveFoldable       #-}
{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE ImpredicativeTypes   #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}


module Check.Solve
  ( Resolver
  , Disambiguating
  , Normaliser
  , Subgoal(..)
  , Reduction(..)
  , Reducer(..)
  , solve

  , contradiction
  , skip
  , solution
  , subgoals
  , tautology
  ) where

import           Check.State
import           Common
import           Introspect
import           Praxis
import           Print
import           Term

import           Control.Monad        (foldM)
import           Data.Maybe           (isJust)
import           Data.Monoid          (Any (..))
import qualified Data.Monoid.Colorful as Colored
import qualified Data.Set             as Set


type Resolver = forall a. Term a => Annotated a -> Maybe (Annotated a)

type Normaliser = forall a. Term a => Annotated a -> Praxis (Annotated a)

type Solution = (Resolver, Normaliser)

data Subgoal c = Subgoal c | Implies c c

data Reduction c = Contradiction | Progress (Maybe Solution) [Subgoal c] | Skip

contradiction = Contradiction

skip = Skip

solution :: Solution -> Reduction c
solution x = Progress (Just x) []

subgoals :: [Subgoal c] -> Reduction c
subgoals x = Progress Nothing x

tautology :: Reduction c
tautology = Progress Nothing []

type Reducer c = c -> Praxis (Reduction c)

type Disambiguating c = Bool -> c

data Tree c = Branch c [Tree c] | Assume c (Tree c)
  deriving (Functor, Foldable, Traversable)

data GoalT x c = Goal x (Tree c)
  deriving (Functor, Foldable, Traversable)

type Crumb c = (Source, Annotation (Requirement c))

type Crumbs c = [Crumb c]

-- Note: Goal definition is split like this for "deriving" to work.
type Goal c = GoalT (Crumbs c) c

instance Pretty (Annotated c) => Pretty (Tree c) where
  pretty (Branch c [])  = pretty (phantom c)
  pretty (Branch c cs)  = pretty (phantom c) <> " (" <> separate ", " cs <> ")" where
  pretty (Assume c1 c2) = pretty (phantom c1) <> " --> " <> pretty c2

instance Pretty (Tree c) => Pretty (GoalT x c) where
  pretty (Goal _ tree) = pretty tree

solve :: forall c a.
  ( Term a
  , Ord c
  , Term c
  , Term (Requirement c)
  , Pretty (Annotation (Requirement c))
  , Ord (Annotation (Requirement c))
  ) => Lens' PraxisState (State c) -> Disambiguating (Reducer c) -> Annotated a -> Praxis (Annotated a)

solve state reduce term = do
  requirements' <- Set.toList <$> use (state . requirements)
  let goals = [ Goal [(src, reason)] (Branch constraint []) | ((src, Just reason) :< Requirement constraint) <- requirements' ]
  (term, [], _) <- solve' False (term, goals)
  return term
  where
    solve' :: Bool -> (Annotated a, [Goal c]) -> Praxis (Annotated a, [Goal c], Bool)
    solve' _ (term, []) = return (term, [], undefined)
    solve' disambiguate (term, goals) = do
      (goals, reduction) <- reduceGoals state (reduce disambiguate) goals
      case reduction of

        TreeProgress
          -> solve' False (term, goals)

        TreeSolved (resolve, normalise) crumbs2
          -> do
            let
              rewrite :: forall a. Term a => Annotated a -> Praxis (Annotated a)
              rewrite = normalise . sub resolve

              rewriteCrumbs :: Crumbs c -> Praxis (Crumbs c)
              rewriteCrumbs = mapM (\(src, reason) -> (src,) <$> (recurseAnnotation (witness :: I (Requirement c)) rewrite reason))

            crumbs2 <- rewriteCrumbs crumbs2

            let
              affectedByRewrite :: forall a. Term a => Annotated a -> Bool
              affectedByRewrite term = getAny (extract f term) where
                f :: forall a. Term a => a -> Any
                f x = Any (isJust (resolve (phantom x)))

              rewriteGoal :: Goal c -> Praxis (Goal c)
              rewriteGoal (Goal crumbs1 tree@(Branch constraint _)) = do
                crumbs1 <- rewriteCrumbs crumbs1
                if affectedByRewrite (phantom constraint)
                  then do
                    tree <- traverse (recurseTerm rewrite) tree
                    let crumbs = crumbs1 ++ [ crumb | crumb <- crumbs2, not (crumb `elem` crumbs1) ]
                    return $ Goal crumbs tree
                  else return (Goal crumbs1 tree)

            term <- rewrite term
            goals <- traverse rewriteGoal goals
            solve' False (term, goals)

        TreeSkip
          | disambiguate -> throw $ "unsolved constraints: " <> separate ", " goals
          | otherwise    -> solve' True (term, goals)


data TreeReduction c = TreeContradiction [c] | TreeProgress | TreeSolved Solution (Crumbs c) | TreeSkip

noskip :: TreeReduction c -> TreeReduction c
noskip TreeSkip = TreeProgress
noskip r        = r

reduceGoals :: forall c.
  ( Term c
  , Ord c
  , Pretty (Annotation (Requirement c))
  ) => Lens' PraxisState (State c) -> Reducer c -> [Goal c] -> Praxis ([Goal c], TreeReduction c)

reduceGoals state reduce = \case

  [] -> return ([], TreeSkip)

  (Goal crumbs tree):goals -> do
    (tree, r1) <- reduceTree state reduce tree
    let
      goal = case tree of
        Just tree -> [Goal crumbs tree]
        Nothing   -> []
    case r1 of
      TreeContradiction trace
        -> throw (printTrace trace)
      TreeProgress -> do
        (goals, r2) <- reduceGoals state reduce goals
        return (goal ++ goals, noskip r2)
      TreeSolved solution _
        -> return (goal ++ goals, TreeSolved solution crumbs)
      TreeSkip ->  do
        (goals, r2) <- reduceGoals state reduce goals
        return (goal ++ goals, r2)
    where
      printTrace :: [c] -> Printable String
      printTrace trace = "unable to satisfy: "  <> pretty (last (c:cs)) <> derived <> printCrumbs crumbs where
        (c:cs) = map phantom trace
        derived = if null cs then blank else "\n  | derived from: " <> pretty c
      printCrumbs :: Crumbs c -> Printable String
      printCrumbs (crumb:crumbs) = primary <> printCrumb crumb <> (if null crumbs then blank else secondary <> separate "\n  | - " (map printCrumb crumbs)) where
        primary = "\n  | " <> pretty (Colored.Style Bold ("primary cause: " :: Colored String))
        secondary = "\n  | " <> (if length crumbs > 1 then "secondary causes:\n  | - " else "secondary cause: ")
      printCrumb :: Crumb c -> Printable String
      printCrumb (src, reason) = pretty reason <> " at " <> pretty (show src)


reduceTree :: forall c.
  ( Ord c
  , Term c
  ) => Lens' PraxisState (State c) -> Reducer c -> Tree c -> Praxis (Maybe (Tree c), TreeReduction c)

-- Note: The supplied assumption may only be used locally (i.e. within 'tree').
-- This means the assumption state needs to be reverted before exiting, to avoid the local assumption *or any consequents* from escaping the local context.
reduceTree state reduce tree = case tree of

  Assume constraint tree -> save (state . assumptions) $ do
    state . assumptions %= (Set.insert constraint)
    reduceTree state reduce tree

  Branch constraint subtrees -> do
    assumptions' <- use (state . assumptions)
    if constraint `Set.member` assumptions'
      then return (Nothing, TreeProgress)
      else case subtrees of
        [] -> do
          -- leaf case (the constraint has not yet been reduced)
          r1 <- reduce constraint
          case r1 of
            Contradiction -> return (Just tree, TreeContradiction [constraint])
            Progress (Just solution) subgoals -> case subgoals of
              [] -> return (Nothing, TreeSolved solution undefined)
              _  -> return (Just (subgoalsToTree subgoals), TreeSolved solution undefined)
            Progress Nothing subgoals -> case subgoals of
              [] -> return (Nothing, TreeProgress)
              _ -> do
                (tree, r2) <- reduceTree state reduce (subgoalsToTree subgoals)
                return (tree, noskip r2)
            Skip -> return (Just tree, TreeSkip)
          where
            subgoalsToTree subgoals = Branch constraint (map subgoalToTree subgoals)
            subgoalToTree = \case
              Subgoal c     -> Branch c []
              Implies c1 c2 -> Assume c1 (Branch c2 [])
        _ -> do
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
  where
    combine :: ([Tree c], TreeReduction c) -> Tree c -> Praxis ([Tree c], TreeReduction c)
    combine (subtrees, r1) subtree = do
      let abort = case r1 of { TreeContradiction _ -> True; TreeSolved _ _ -> True; _ -> False }
      if abort
        then return (subtree : subtrees, r1)
        else do
          (subtree, r2) <- reduceTree state reduce subtree
          let
            r3 = case r1 of
              TreeSkip     -> r2
              TreeProgress -> noskip r2
          let
            subtrees' = case subtree of
              Nothing      -> subtrees
              Just subtree -> subtree : subtrees
          return (subtrees', r3)
