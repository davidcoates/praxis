{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Check.Solve
  ( solve
  ) where

import           AST
import           Check.Derivation
import           Check.System
import           Effect
import           Error
import           Praxis
import           Record
import           Sub
import           Type
import           Vars

import           Control.Applicative    (Const (..))
import           Control.Arrow          (second)
import           Control.Monad.Identity (Identity (..))
import           Data.List              (nub, sort)
import           Data.Maybe             (fromJust)
import           Data.Set               (Set, union)
import qualified Data.Set               as Set
import           Prelude                hiding (log)

instance Vars Derivation where
  vars d = vars (constraint d)

instance Vars Constraint where
  vars (EqualP p1 p2) = vars p1 `mappend` vars p2
  vars (EqualE e1 e2) = vars e1 `mappend` vars e2
  vars (Class _ t)    = vars t


solve :: [Derivation] -> Praxis [(String, Term)]
solve cs = save stage $ save system $ do
  set stage Solve
  set system (initialSystem cs)
  spin
  sol <- get (system . solution)
  logList Debug (sort sol)
  return sol

spin :: Praxis ()
spin = do
  set (system . changed) False
  progress
  thinking <- get (system . changed)
  if thinking then
    spin
  else do
    cs <- get (system . constraints)
    case cs of [] -> return () -- Done
               _  -> logList Normal cs >> throwError (CheckError Stuck)

progress :: Praxis ()
progress = do
  cs <- (nub . sort) <$> get (system . constraints)
  set (system . constraints) []
  set (system . staging) cs
  progress'

progress' :: Praxis ()
progress' = do
  cs <- get (system . staging)
  case cs of []     -> return () -- Done
             (c:cs) -> set (system . staging) cs >> (single c >>= (\cs -> over (system . constraints) (++ cs))) >> progress'

single :: Derivation -> Praxis [Derivation]
single d = case constraint d of

  EqualE e1 e2 | e1 == e2                      -> tautology
               | e1 >  e2                      -> swap -- We save handling symmetric cases below by careful definition of Ord for Effect/Effects
               | [EfUni n] <- Effect.toList e1 -> if n `elem` unisE e2 then defer else n ↦ TermEffects e2
               | []        <- Effect.toList e1 -> let empty (EfUni n) = n ↦ TermEffects Effect.empty
                                                      empty _         = contradiction
                                                  in foldr (\a b -> empty a >> b) solved (Effect.toList e2)
               | otherwise                     -> defer

  EqualP p1 p2 | p1 == p2 -> tautology

  EqualP (TyUni x)           p -> if x `elem` unisP p then contradiction else x ↦ TermPure p
  EqualP _           (TyUni _) -> swap

  EqualP (TyFun p1 (p2 :# e2)) (TyFun p3 (p4 :# e4)) -> introduce [ EqualP p1 p3, EqualP p2 p4, EqualE e2 e4 ]

  EqualP (TyRecord r1) (TyRecord r2) | sort (keys r1) == sort (keys r2) -> let values = map snd . Record.toCanonicalList
                                                                           in  introduce (zipWith EqualP (values r1) (values r2))

  EqualP _ _ -> contradiction

  Class "Share" p -> case p of
    TyPrim _   -> tautology
    TyFun _ _  -> tautology
    TyUni _    -> defer
    TyRecord r -> introduce (map (Class "Share" . snd) (Record.toList r))
    _          -> contradiction

  Class _ p -> defer

  where solved = set (system . changed) True >> pure []
        tautology = solved
        defer = pure [d]
        introduce cs = set (system . changed) True >> pure (map (d `implies`) cs)
        swap = case constraint d of EqualP p1 p2 -> single d{ constraint = EqualP p2 p1 }
                                    EqualE e1 e2 -> single d{ constraint = EqualE e2 e1 }
        contradiction = throwError . CheckError . Contradiction $ d
        (↦) :: Name -> Term -> Praxis [Derivation]
        n ↦ p = do
          let f :: Sub a => a -> a
              f = sub (\n' -> if n == n' then Just p else Nothing)
          over (system . solution) ((n, p):)
          over (system . solution) (map (second f))
          over (system . constraints) (map f)
          over (system . staging) (map f)
          over (system . axioms) (map f)
          over tEnv (fmap f)
          set (system . changed) True
          return []
