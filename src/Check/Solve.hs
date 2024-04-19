{-# LANGUAGE DeriveFoldable      #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ImpredicativeTypes  #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE TupleSections       #-}


module Check.Solve
  ( Resolver
  , Normaliser
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
import           Data.Maybe    (isJust)
import           Data.Monoid   (Any (..))
import qualified Data.Set      as Set


type Resolver = forall a. Term a => Annotated a -> Maybe (Annotated a)

type Normaliser = forall a. Term a => Annotated a -> Praxis (Annotated a)

type Solution = (Resolver, Normaliser)

data Reduction c = Contradiction | Skip | Solved Solution | Subgoals [c] | Tautology

type Reducer c = c -> Praxis (Reduction c)

data Tree c = Branch c [Tree c]
  deriving (Functor, Foldable, Traversable)

data GoalT x c = Goal x (Tree c)
  deriving (Functor, Foldable, Traversable)

type Crumb c = (Source, Annotation (Requirement c))

type Crumbs c = [Crumb c]

-- Note: Goal definition is split like this for "deriving" to work.
type Goal c = GoalT (Crumbs c) c


solve :: forall c a.
  ( Term a
  , Ord c
  , Term c
  , Term (Requirement c)
  , Pretty (Annotation (Requirement c))
  , Ord (Annotation (Requirement c))
  ) => Lens' PraxisState (System c) -> Reducer c -> Annotated a -> Praxis (Annotated a)

solve system reduce term = do
  requirements' <- use (system . requirements)
  let goals = [ Goal [(src, reason)] (Branch constraint []) | ((src, Just reason) :< Requirement constraint) <- requirements' ]
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
            (system . assumptions) %%= (\as -> Set.fromList <$> (traverse (recurseTerm rewrite) (Set.toList as)))
            solve' (term, goals)

        TreeSkip -- Shouldn't happen...
          -> throw ("!!! failed to solve constraints !!!" :: String)


data TreeReduction c = TreeContradiction [c] | TreeProgress | TreeSolved Solution (Crumbs c) | TreeSkip

noskip :: TreeReduction c -> TreeReduction c
noskip TreeSkip = TreeProgress
noskip r        = r

reduceGoals :: forall c. (Term c, Ord c, Pretty (Annotation (Requirement c))) => Lens' PraxisState (System c) -> Reducer c -> [Goal c] -> Praxis ([Goal c], TreeReduction c)
reduceGoals system reduce [] = return ([], TreeSkip)
reduceGoals system reduce ((Goal crumbs tree):goals) = do
  (tree, r1) <- reduceTree system reduce tree
  let
    goal = case tree of
      Just tree -> [Goal crumbs tree]
      Nothing   -> []
  case r1 of
    TreeContradiction trace
      -> throw (printTrace trace)
    TreeProgress -> do
      (goals, r2) <- reduceGoals system reduce goals
      return (goal ++ goals, noskip r2)
    TreeSolved solution _
      -> return (goal ++ goals, TreeSolved solution crumbs)
    TreeSkip ->  do
      (goals, r2) <- reduceGoals system reduce goals
      return (goal ++ goals, r2)
  where
    printTrace :: [c] -> Printable String
    printTrace trace = "unable to satisfy: "  <> pretty (last (c:cs)) <> derived <> printCrumbs crumbs where
      (c:cs) = map phantom trace
      derived = if null cs then blank else "\n  | derived from: " <> pretty c
    printCrumbs :: Crumbs c -> Printable String
    printCrumbs (crumb:crumbs) = primary <> printCrumb crumb <> (if null crumbs then blank else secondary <> separate "\n  | - " (map printCrumb crumbs)) where
      primary = "\n  | " <> pretty (Style Bold ("primary cause: " :: Colored String))
      secondary = "\n  | " <> (if length crumbs > 1 then "secondary causes:\n  | - " else "secondary cause: ")
    printCrumb :: Crumb c -> Printable String
    printCrumb (src, reason) = pretty reason <> " at " <> pretty (show src)


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
        Solved solution   -> return (Nothing, TreeSolved solution undefined)
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
      let abort = case r1 of { TreeContradiction _ -> True; TreeSolved _ _ -> True; _ -> False }
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
