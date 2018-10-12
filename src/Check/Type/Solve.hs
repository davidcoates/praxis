{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Check.Type.Solve
  ( solve
  ) where

import           AST
import           Check.Type.Annotate
import           Check.Type.Constraint
import           Check.Type.System
import           Common
import           Env.TEnv               (ungeneralise)
import           Error
import           Praxis
import           Record
import           Source
import           Tag
import           Type

import           Control.Applicative    (Const (..), liftA2)
import           Control.Monad.Identity (Identity (..))
import           Data.List              (nub, sort)
import           Data.Maybe             (fromMaybe)
import           Data.Set               (Set, union)
import qualified Data.Set               as Set
import           Prelude                hiding (log)

solve :: Praxis ([(Name, Typed Type)], [(Name, Typed QType)])
solve = undefined
{-
solve = save stage $ save system $ do
  put stage Solve
  solve'
  tySol <- get (system . tySol)
  kindSol <- get (system . kindSol)
  return (tySol, kindSol)

data State = Cold
           | Warm
           | Done

solve' :: Praxis State
solve' = spin progress `chain` spin generalise `chain` stuck
    where chain :: Praxis State -> Praxis State -> Praxis State
          chain p1 p2 = p1 >>= \s -> case s of
            Cold -> p2
            Warm -> solve'
            Done -> return Done
          stuck = do
            cs <- get (system . constraints)
            logList Normal cs
            throwError (CheckError Stuck)

spin :: (Derivation -> Praxis Bool) -> Praxis State
spin solve = do
  cs <- (nub . sort) <$> get (system . constraints)
  case cs of
    [] -> return Done
    _  -> do
      put (system . constraints) []
      put (system . staging) cs
      warm <- loop
      return $ if warm then Warm else Cold
  where
    loop = do
      cs <- get (system . staging)
      case cs of
        []     -> return False
        (c:cs) -> put (system . staging) cs >> liftA2 (||) (solve c) loop

generalise :: Derivation -> Praxis Bool
generalise d = do
  ds <- liftA2 (++) (get (system . constraints)) (get (system . staging))
  case constraint d of
    Generalises (_ :< QTyUni n) t -> generalise' ds n t
    Generalises _               _ -> error "unreachable?"
    _                             -> defer
  where
    defer = require d >> return False
    generalise' :: [Derivation] -> Name -> Kinded Type -> Praxis Bool
    generalise' ds n t = case classes (extract unis t) ds of
      Nothing -> defer
      Just ts -> qTySolve n (generaliseType ts t)

generaliseType :: [Kinded Type] -> Kinded Type -> Kinded QType
generaliseType ts (a :< t) = case us of
  [] -> a :< Mono t
  _  -> undefined -- TODO For each uni in t, find an annotated kind. Use this to build up [(Name, Kind)]
  where us = extract unis (a :< t)
        vs = map (:[]) ['a'..]
        f u = (`lookup` zip us vs)

-- TODO use sets here?
classes :: [Name] -> [Derivation] -> Maybe [Kinded Type]
classes ns cs = (\f -> concat <$> mapM f cs) $ \d -> case constraint d of
  Class t         -> let ns' = extract unis t in if all (`elem` ns) ns' then Just [t] else if any (`elem` ns') ns then Nothing else Just []
  EqKind k1 k2    -> if any (`elem` (extract unis k1 ++ extract unis k2)) ns then Nothing else Just []
  EqType t1 t2    -> if any (`elem` (extract unis t1 ++ extract unis t2)) ns then Nothing else Just []
  Generalises q t -> Just [] -- TODO not sure about these
  Specialises t q -> Just []


progress :: Derivation -> Praxis Bool
progress d = case constraint d of

  Class (k1 :< TyApply (k2 :< TyCon "Share") (a :< p)) -> case p of -- TODO Need instance solver!
    TyApply (_ :< TyCon "->") _ -> tautology
    TyUni _                     -> defer
    TyCon n | n `elem` ["Int", "Char", "Bool"] -> tautology
    TyRecord r                  -> introduce (map ((\t -> Class (k1 :< TyApply (k2 :< TyCon "Share") t)). snd) (Record.toList r))
    _                           -> contradiction

  EqKind k1 k2 | k1 == k2  -> tautology

  EqKind (KindUni x) k -> if x `elem` extract unis k then contradiction else kindSolve x k
  EqKind _ (KindUni _) -> swap

  EqKind (KindRecord r1) (KindRecord r2) | sort (keys r1) == sort (keys r2) ->
    let values = map snd . Record.toCanonicalList in introduce (zipWith EqKind (values r1) (values r2)) -- TODO create zipRecord or some such

  EqKind (KindFun t1 t2) (KindFun t3 t4) -> introduce [ EqKind t1 t3, EqKind t2 t4 ]

  EqKind _ _ -> contradiction

  -- TODO do we need to do kind checking all through here?
  EqType t1 t2 | t1 == t2 -> tautology

  EqType (_ :< TyUni x) t -> if x `elem` extract unis t then contradiction else tySolve x t
  EqType _ (_ :< TyUni _) -> swap

  EqType (_ :< TyApply n1 t1) (_ :< TyApply n2 t2) | n1 == n2  -> introduce [ EqType t1 t2 ]

  EqType (_ :< TyPack r1) (_ :< TyPack r2) | sort (keys r1) == sort (keys r2) ->
    let values = map snd . Record.toCanonicalList in introduce (zipWith EqType (values r1) (values r2)) -- TODO create zipRecord or some such

  EqType (_ :< TyRecord r1) (_ :< TyRecord r2) | sort (keys r1) == sort (keys r2) ->
    let values = map snd . Record.toCanonicalList in introduce (zipWith EqType (values r1) (values r2)) -- TODO create zipRecord or some such

  EqType (_ :< TyApply n1 t1) (_ :< TyApply n2 t2) | n1 == n2  -> introduce [ EqType t1 t2 ]

  EqType t1@(_ :< TyEffects e1) t2@(_ :< TyEffects e2) -- Consider if we have unis, but they aren't of kind effect?
    | e1 > e2 -> swap
    | [_ :< TyUni n] <- Set.toList e1 -> if n `elem` extract unis t2 then defer else tySolve n t2
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
            defer
            -- FIXME This isn't correct! We could add any subset of l1 to n1
            -- tySolve n1 (KindEffect :< TyEffects (Set.difference e2 l1)) -- TODO for all these differences, need to flatten?
          else
            contradiction
        else
          defer
    | null (extract unis t1 ++ extract unis t2) -> contradiction
    | otherwise                     -> defer

  Specialises _ (_ :< QTyUni _) -> defer

  Specialises t q -> do
    t' <- ungeneralise Phantom q
    introduce [ EqType t t' ]

  Generalises _ _ -> defer

  _ -> contradiction

  where solved = return True
        tautology = solved
        defer = require d >> return False
        contradiction = throwError . CheckError . Contradiction $ d
        introduce cs = requireAll (map (d `implies`) cs) >> return True
        swap = case constraint d of EqType t1 t2 -> progress d{ constraint = EqType t2 t1 }
                                    EqKind k1 k2 -> progress d{ constraint = EqKind k2 k1 }

        snake :: Set (Kinded Type) -> Maybe (Name, Set (Kinded Type))
        snake es = case Set.toList es of
          ((_ :< TyUni n):es) -> if null (concatMap (extract unis) es) then Just (n, Set.fromList es) else Nothing
          _                   -> Nothing

        literals :: Set (Kinded Type) -> Bool
        literals es = null (concatMap (extract unis) (Set.toList es))

qTySolve :: Name -> Kinded QType -> Praxis Bool
qTySolve n q = do
  let f :: Kinded QType -> Praxis (Kinded QType)
      f = pure . subs (\n' -> if n == n' then Just q else Nothing)
  over (system . qTySol) ((n, q):)
  modify system (pseudoTraverse f)
  modify tEnv (traverse f)
  reuse n
  return True

tySolve :: Name -> Kinded Type -> Praxis Bool
tySolve n p = do
  let f :: Kinded Type -> Praxis (Kinded Type)
      f = tyGenSub (\n' -> if n == n' then Just p else Nothing)
  over (system . tySol) ((n, p):)
  modify system (pseudoTraverse f)
  modify tEnv (traverse (pseudoTraverse f))
  reuse n
  return True

kindSolve :: Name -> Kind -> Praxis Bool
kindSolve n p = do
  let f :: Kind -> Praxis Kind
      f = pure . subs (\n' -> if n == n' then Just p else Nothing)
  over (system . kindSol) ((n, p):)
  modify system (pseudoTraverse f)
  modify tEnv (traverse (pseudoTraverse f))
  modify kEnv (traverse f)
  reuse n
  return True

tyGenSub :: TypeTraversable a => (Name -> Maybe (Kinded Type)) -> a -> Praxis a
tyGenSub f = pseudoTraverse f'
    where
      f' (k :< t) = case t of
        TyUni n -> case f n of
          Just (k' :< t')  -> do
            require $ newDerivation (EqKind k k') (Custom "TODO tyGenSub") Phantom -- TODO
            return (k' :< t')
          Nothing          -> return (k :< t)
        _       -> return (k :< t)
-}
