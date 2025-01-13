{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Check.Solve
  ( Resolver
  , Disambiguating
  , Normalizer
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

import           Check.State          (Constraint (..), SolveState, assumptions,
                                       requirements)
import           Common
import           Introspect
import           Praxis
import           Print
import           Stage
import           Term

import           Control.Monad        (foldM)
import           Data.Maybe           (isJust)
import           Data.Monoid          (Any (..))
import qualified Data.Monoid.Colorful as Colored
import qualified Data.Set             as Set


type Resolver s = forall a. IsTerm a => Annotated s a -> Maybe (Annotated s a)

type Normalizer s = forall a. IsTerm a => Annotated s a -> Praxis (Annotated s a)

type Solution s = (Resolver s, Normalizer s)

data Subgoal s = Subgoal (Annotated s (Constraint s)) | Implies (Annotated s (Constraint s)) (Annotated s (Constraint s))

data Reduction s = Contradiction | Progress (Maybe (Solution s)) [Subgoal s] | Skip

contradiction = Contradiction

skip = Skip

solution :: Solution s -> Reduction s
solution x = Progress (Just x) []

subgoals :: [Subgoal s] -> Reduction s
subgoals x = Progress Nothing x

tautology :: Reduction s
tautology = Progress Nothing []

type Reducer s = (Annotated s (Constraint s)) -> Praxis (Reduction s)

type Disambiguating a = Bool -> a

-- Note: Goal definition is split like this for "deriving" to work.
data TreeT c = Branch c [TreeT c] | Assume c (TreeT c)
  deriving (Functor, Foldable, Traversable)

type Tree s = TreeT (Annotated s (Constraint s))

data GoalT x c = Goal x (TreeT c)
  deriving (Functor, Foldable, Traversable)

type Crumb s = (Source, Annotation s (Requirement (Constraint s)))

type Crumbs s = [Crumb s]

-- Note: Goal definition is split like this for "deriving" to work.
type Goal s = GoalT (Crumbs s) (Annotated s (Constraint s))

instance Pretty c => Pretty (TreeT c) where
  pretty (Branch c [])  = pretty c
  pretty (Branch c cs)  = pretty c <> " (" <> separate ", " cs <> ")" where
  pretty (Assume c1 c2) = pretty c1 <> " --> " <> pretty c2

instance Pretty (TreeT c) => Pretty (GoalT x c) where
  pretty (Goal _ tree) = pretty tree

solve :: forall s c a.
  ( IsTerm a
  , IsStage s
  , Ord (c s)
  , IsTerm c
  , IsTerm (Requirement c)
  , Pretty (Annotation s (Requirement c))
  , Ord (Annotation s (Requirement c))
  , Constraint s ~ c
  ) => Lens' PraxisState (SolveState s) -> Disambiguating (Reducer s) -> Annotated s a -> Praxis (Annotated s a)

solve state reduce term = do
  requirements' <- Set.toList <$> use (state . requirements)
  let goals = [ Goal [(src, reason)] (Branch constraint []) | ((src, reason) :< Requirement constraint) <- requirements' ]
  (term, [], _) <- solve' False (term, goals)
  return term
  where
    solve' :: Bool -> (Annotated s a, [Goal s]) -> Praxis (Annotated s a, [Goal s], Bool)
    solve' _ (term, []) = return (term, [], undefined)
    solve' disambiguate (term, goals) = do
      (goals, reduction) <- reduceGoals state (reduce disambiguate) goals
      case reduction of

        TreeProgress
          -> solve' False (term, goals)

        TreeSolved (resolve, normalize) crumbs2
          -> do
            let
              rewrite :: forall a. (IsTerm a, IsStage s) => Annotated s a -> Praxis (Annotated s a)
              rewrite = normalize . sub resolve

              rewriteCrumbs :: Crumbs s -> Praxis (Crumbs s)
              rewriteCrumbs = traverse (\(src, reason) -> (\a -> (src, a)) <$> (recurseAnnotation (stageT :: StageT s) (termT :: TermT (Requirement c)) rewrite reason))

            crumbs2 <- rewriteCrumbs crumbs2

            let
              affectedByRewrite :: forall a. IsTerm a => Annotated s a -> Bool
              affectedByRewrite term = getAny (extract f term) where
                f :: forall a. IsTerm a => Annotated s a -> Any
                f x = Any (isJust (resolve x))

              rewriteGoal :: Goal s -> Praxis (Goal s)
              rewriteGoal (Goal crumbs1 tree@(Branch constraint _)) = do
                crumbs1 <- rewriteCrumbs crumbs1
                if affectedByRewrite constraint
                  then do
                    tree <- traverse (recurse rewrite) tree
                    let crumbs = crumbs1 ++ [ crumb | crumb <- crumbs2, not (crumb `elem` crumbs1) ]
                    return $ Goal crumbs tree
                  else return (Goal crumbs1 tree)

            term <- rewrite term
            goals <- traverse rewriteGoal goals
            solve' False (term, goals)

        TreeSkip
          | disambiguate -> throw (stageToEnum (stageT :: StageT s)) $ "unsolved constraints: " <> separate ", " goals
          | otherwise    -> solve' True (term, goals)


data TreeReduction s = TreeContradiction [Annotated s (Constraint s)] | TreeProgress | TreeSolved (Solution s) (Crumbs s) | TreeSkip

noskip :: TreeReduction s -> TreeReduction s
noskip TreeSkip = TreeProgress
noskip r        = r

reduceGoals :: forall s c.
  ( IsTerm c
  , IsStage s
  , Ord (c s)
  , Pretty (Annotation s (Requirement c))
  , Constraint s ~ c
  ) => Lens' PraxisState (SolveState s) -> Reducer s -> [Goal s] -> Praxis ([Goal s], TreeReduction s)

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
        -> throw (stageToEnum (stageT :: StageT s)) (printTrace trace)
      TreeProgress -> do
        (goals, r2) <- reduceGoals state reduce goals
        return (goal ++ goals, noskip r2)
      TreeSolved solution _
        -> return (goal ++ goals, TreeSolved solution crumbs)
      TreeSkip ->  do
        (goals, r2) <- reduceGoals state reduce goals
        return (goal ++ goals, r2)
    where
      printTrace :: [Annotated s c] -> Colored String
      printTrace (c:cs) = "unable to satisfy: "  <> pretty (last (c:cs)) <> derived <> printCrumbs crumbs where
        derived = if null cs then Colored.Nil else "\n  | derived from: " <> pretty c
      printCrumbs :: Crumbs s -> Colored String
      printCrumbs (crumb:crumbs) = primary <> printCrumb crumb <> (if null crumbs then Colored.Nil else secondary <> separate "\n  | - " (map printCrumb crumbs)) where
        primary = "\n  | " <> pretty (Colored.Style Bold ("primary cause: " :: Colored String))
        secondary = "\n  | " <> (if length crumbs > 1 then "secondary causes:\n  | - " else "secondary cause: ")
      printCrumb :: Crumb s -> Colored String
      printCrumb (src, reason) = pretty reason <> " at " <> pretty (show src)


reduceTree :: forall s c.
  ( Ord (c s)
  , IsTerm c
  , IsStage s
  , Constraint s ~ c
  ) => Lens' PraxisState (SolveState s) -> Reducer s -> Tree s -> Praxis (Maybe (Tree s), TreeReduction s)

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
    combine :: ([Tree s], TreeReduction s) -> Tree s -> Praxis ([Tree s], TreeReduction s)
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
