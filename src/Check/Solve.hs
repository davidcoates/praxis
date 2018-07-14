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
import           Source
import           Tag
import           Type

import           Control.Applicative    (Const (..), liftA2)
import           Control.Arrow          (second)
import           Control.Monad.Identity (Identity (..))
import           Data.List              (nub, sort)
import           Data.Maybe             (fromMaybe)
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
    | [_ :< TyUni n] <- Set.toList e1 -> if n `elem` tyUnis t2 then defer else tySolve n t2
    | []             <- Set.toList e1 -> let empty (_ :< TyUni n) = tySolve n (KindEffect :< TyEffects Set.empty)
                                             empty _              = contradiction
                                         in foldr (\a b -> empty a >> b) solved e2
    | Just ((n1, l1), (n2, l2)) <- liftA2 (,) (snake e1) (snake e2) ->
        if n1 == n2 then do
          a <- freshUniE
          tySolve n1 (KindEffect :< TyEffects (Set.unions [Set.singleton a, Set.difference l2 l1, Set.difference l1 l2]))
        else
          tySolve n1 (KindEffect :< TyEffects (Set.union (Set.difference l2 l1) (Set.singleton (KindEffect :< TyUni n2)))) -- TODO adding KindEffects, is this a problem?
    | Just (n1, l1) <- snake e1 ->
        if literals e2 then
          if Set.isSubsetOf l1 e2 then
            tySolve n1 (KindEffect :< TyEffects (Set.difference e2 l1)) -- TODO for all these differences, need to flatten?
          else
            contradiction
        else
          defer
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

        snake :: Set (Kinded Type) -> Maybe (Name, Set (Kinded Type))
        snake es = case Set.toList es of
          ((_ :< TyUni n):es) -> if null (tyUnis es) then Just (n, Set.fromList es) else Nothing
          _                   -> Nothing

        literals :: Set (Kinded Type) -> Bool
        literals es = null (tyUnis (Set.toList es))

        tySolve :: Name -> Kinded Type -> Praxis [Derivation]
        tySolve n p = do
          let f :: TypeTraversable a => a -> Special Derivation a
              f = tyGenSub (\n' -> if n == n' then Just p else Nothing)
              lift f = runSpecial . sequenceA . map f
          over (system . tySol) ((n, p):)
          cs <- sequence
            [ extract (system . tySol) (lift (\(n, t) -> (\t -> (n, t)) <$> f t))
            , extract (system . constraints) (lift f)
            , extract (system . staging) (lift f)
            , extract (system . axioms) (lift f)
            , extract tEnv (runSpecial . sequenceA . fmap f)
            ]
          set (system . changed) True
          reuse n
          return (concat cs)
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
          reuse n
          return []

 -- typeTraverse :: Applicative f => (Kinded Type -> f (Kinded Type)) -> a -> f a

newtype Special a b = Special { runSpecial :: ([a], b) }

instance Functor (Special a) where
  fmap f (Special (cs, x)) = Special (cs, f x)

instance Applicative (Special a) where
  pure x = Special ([], x)
  liftA2 f (Special (c1, x)) (Special (c2, y)) = Special (c1 ++ c2, f x y)

tyGenSub :: TypeTraversable a => (Name -> Maybe (Kinded Type)) -> a -> Special Derivation a
tyGenSub f = typeTraverse (Special . f')
    where
      f' (k :< t) = case t of
        TyUni n -> case f n of
          Just (k' :< t')  -> ([ newDerivation (EqKind k k') (Custom "TODO tyGenSub") Phantom ], k' :< t') -- TODO
          Nothing          -> return (k :< t)
        _       -> return (k :< t)
