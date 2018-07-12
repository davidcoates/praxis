{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Check.Solve
  ( solve
  ) where

import           AST
import           Check.Constraint
import           Check.System
import           Error
import           Praxis
import           Record
import           Tag
import           Type

import           Control.Applicative    (Const (..))
import           Control.Arrow          (second)
import           Control.Monad.Identity (Identity (..))
import           Data.List              (nub, sort)
import           Data.Maybe             (fromJust)
import           Data.Set               (Set, union)
import qualified Data.Set               as Set
import           Prelude                hiding (log)

solve :: [Derivation] -> Praxis ([(Name, Kinded Type)], [(Name, Kind)])
solve cs = save stage $ save system $ do
  set stage Solve
  set system (initialSystem cs)
  spin
  tySol <- get (system . tySol)
  kindSol <- get (system . kindSol)
  logList Debug tySol
  logList Debug kindSol
  return (tySol, kindSol)

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
  cs <- get (system . staging)
  case cs of []     -> return () -- Done
             (c:cs) -> set (system . staging) cs >> (single c >>= (\cs -> over (system . constraints) (++ cs))) >> progress'

single :: Derivation -> Praxis [Derivation]
single d = case constraint d of

  Class (k1 :< TyApply (k2 :< TyCon "Share") (a :< p)) -> case p of -- TODO Need instance solver!
    TyApply (_ :< TyCon "->") _ -> tautology
    TyUni _                     -> defer
    TyCon n | n `elem` ["Int", "Char", "Bool"] -> tautology
    TyRecord r                  -> introduce (map ((\t -> Class (k1 :< TyApply (k2 :< TyCon "Share") t)). snd) (Record.toList r))
    _                           -> contradiction

  EqKind k1 k2 | k1 == k2  -> tautology

  EqKind (KindUni x) k -> if x `elem` kindUnis k then contradiction else kindSolve x k
  EqKind _ (KindUni _) -> swap

  EqKind (KindRecord r1) (KindRecord r2) | sort (keys r1) == sort (keys r2) ->
    let values = map snd . Record.toCanonicalList in introduce (zipWith EqKind (values r1) (values r2)) -- TODO create zipRecord or some such

  EqKind (KindFun t1 t2) (KindFun t3 t4) -> introduce [ EqKind t1 t3, EqKind t2 t4 ]

  EqKind _ _ -> contradiction

  -- TODO do we need to do kind checking all through here?
  EqType t1 t2 | t1 == t2 -> tautology

  EqType (_ :< TyUni x) t -> if x `elem` tyUnis t then contradiction else tySolve x t
  EqType _ (_ :< TyUni _) -> swap

  EqType (_ :< TyApply n1 t1) (_ :< TyApply n2 t2) | n1 == n2  -> introduce [ EqType t1 t2 ]

  EqType (_ :< TyPack r1) (_ :< TyPack r2) | sort (keys r1) == sort (keys r2) ->
    let values = map snd . Record.toCanonicalList in introduce (zipWith EqType (values r1) (values r2)) -- TODO create zipRecord or some such

  EqType (_ :< TyRecord r1) (_ :< TyRecord r2) | sort (keys r1) == sort (keys r2) ->
    let values = map snd . Record.toCanonicalList in introduce (zipWith EqType (values r1) (values r2)) -- TODO create zipRecord or some such

  EqType (_ :< TyApply n1 t1) (_ :< TyApply n2 t2) | n1 == n2  -> introduce [ EqType t1 t2 ]

  EqType t1@(_ :< TyEffects e1) t2@(_ :< TyEffects e2) -- Consider if we have unis, but they aren't of kind effect?
    | e1 > e2 -> swap
    | [_ :< TyUni n] <- e1 -> if n `elem` tyUnis t1 then defer else tySolve n t2
    | []             <- e1 -> let empty (_ :< TyUni n) = tySolve n (KindEffect :< TyEffects [])
                                  empty _              = contradiction
                               in foldr (\a b -> empty a >> b) solved e2
    | null (tyUnis t1 ++ tyUnis t2) -> contradiction
    | otherwise                     -> defer
  _ -> contradiction

  where solved = set (system . changed) True >> pure []
        tautology = solved
        defer = pure [d]
        contradiction = throwError . CheckError . Contradiction $ d
        introduce cs = set (system . changed) True >> pure (map (d `implies`) cs)
        swap = case constraint d of EqType t1 t2 -> single d{ constraint = EqType t2 t1 }
                                    EqKind k1 k2 -> single d{ constraint = EqKind k2 k1 }
        tySolve :: Name -> Kinded Type -> Praxis [Derivation]
        tySolve n p = do
          let f :: TypeTraversable a => a -> a
              f = tySub (\n' -> if n == n' then Just p else Nothing)
          over (system . tySol) ((n, p):)
          over (system . tySol) (map (second f))
          over (system . constraints) (map f)
          over (system . staging) (map f)
          over (system . axioms) (map f)
          over tEnv (fmap f)
          set (system . changed) True
          return []
        kindSolve :: Name -> Kind -> Praxis [Derivation]
        kindSolve n p = do
          let f :: KindTraversable a => a -> a
              f = kindSub (\n' -> if n == n' then Just p else Nothing)
          over (system . kindSol) ((n, p):)
          over (system . kindSol) (map (second f))
          over (system . tySol) (map (second f))
          over (system . constraints) (map f)
          over (system . staging) (map f)
          over (system . axioms) (map f)
          over tEnv (fmap f)
          over kEnv (fmap f)
          set (system . changed) True
          return []
