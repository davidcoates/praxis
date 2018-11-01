{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Check.Type.Solve
  ( solve
  ) where

import           AST
import           Check.Type.Annotate
import           Check.Type.Constraint
import           Check.Type.Require
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
solve = save stage $ save our $ do
  stage .= TypeCheck Solve
  solve'
  t <- get (our . tsol)
  q <- get (our . qsol)
  return (t, q)

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
-- FIXME
--            cs <- get (our . constraints)
--            logList Normal cs
            throwError (CheckError Stuck)

spin :: (Derivation -> Praxis Bool) -> Praxis State
spin solve = do
  cs <- (nub . sort) <$> get (our . constraints)
  case cs of
    [] -> return Done
    _  -> do
      our . constraints .= []
      our . staging .= cs
      warm <- loop
      return $ if warm then Warm else Cold
  where
    loop = do
      cs <- get (our . staging)
      case cs of
        []     -> return False
        (c:cs) -> (our . staging .= cs) >> liftA2 (||) (solve c) loop

generalise :: Typed (Const Constraint) -> Praxis Bool
generalise d = do
  ds <- liftA2 (++) (get (our . constraints)) (get (our . staging))
  case constraint d of
    Generalises (_ :< QTyUni n) t -> generalise' ds n t
    Generalises _               _ -> error "unreachable?"
    _                             -> defer
  where
    defer = require d >> return False
    generalise' :: [Derivation] -> Name -> Typed Type -> Praxis Bool
    generalise' ds n t = case classes (extract unis t) ds of
      Nothing -> defer
      Just ts -> qTySolve n (generaliseType ts t)

generaliseType :: [Typed Type] -> Typed Type -> Typed QType
generaliseType ts (a :< t) = case us of
  [] -> a :< Mono t
  _  -> undefined -- TODO For each uni in t, find an annotated kind. Use this to build up [(Name, Kind)]
  where us = extract unis (a :< t)
        vs = map (:[]) ['a'..]
        f u = (`lookup` zip us vs)

-- TODO use sets here?
classes :: [Name] -> [Typed (Const Constraint)] -> Maybe [Typed Type]
classes ns cs = (\f -> concat <$> mapM f cs) $ \d -> case constraint d of
  Class t         -> let ns' = extract unis t in if all (`elem` ns) ns' then Just [t] else if any (`elem` ns') ns then Nothing else Just []
  Eq t1 t2    -> if any (`elem` (extract unis t1 ++ extract unis t2)) ns then Nothing else Just []
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

  Eq t1 t2 | t1 == t2 -> tautology

  Eq (_ :< TyUni x) t -> if x `elem` extract unis t then contradiction else tySolve x t
  Eq _ (_ :< TyUni _) -> swap

  Eq (_ :< TyApply n1 t1) (_ :< TyApply n2 t2) | n1 == n2  -> introduce [ Eq t1 t2 ]

  Eq (_ :< TyPack r1) (_ :< TyPack r2) | sort (keys r1) == sort (keys r2) ->
    let values = map snd . Record.toCanonicalList in introduce (zipWith Eq (values r1) (values r2)) -- TODO create zipRecord or some such

  Eq (_ :< TyRecord r1) (_ :< TyRecord r2) | sort (keys r1) == sort (keys r2) ->
    let values = map snd . Record.toCanonicalList in introduce (zipWith Eq (values r1) (values r2)) -- TODO create zipRecord or some such

  Eq (_ :< TyApply n1 t1) (_ :< TyApply n2 t2) | n1 == n2  -> introduce [ Eq t1 t2 ]

  Eq t1@(_ :< TyFlat e1) t2@(_ :< TyFlat e2)
    | e1 > e2 -> swap
    | [_ :< TyUni n] <- Set.toList e1 -> if n `elem` extract unis t2 then defer else tySolve n t2
    | []             <- Set.toList e1 -> let empty (_ :< TyUni n) = tySolve n (TyFlat Set.empty)
                                             empty _              = contradiction
                                         in foldr (\a b -> empty a >> b) solved e2
    | Just ((n1, l1), (n2, l2)) <- liftA2 (,) (snake e1) (snake e2) ->
        if n1 == n2 then do
          a <- freshUniE
          tySolve n1 (KindEffect :< TyFlat (Set.unions [Set.singleton a, Set.difference l2 l1, Set.difference l1 l2]))
        else
          tySolve n1 (KindEffect :< TyFlat (Set.union (Set.difference l2 l1) (Set.singleton (KindEffect :< TyUni n2)))) -- TODO adding KindEffects, is this a problem?
    | Just (n1, l1) <- snake e1 ->
        if literals e2 then
          if Set.isSubsetOf l1 e2 then
            defer
            -- FIXME This isn't correct! We could add any subset of l1 to n1
            -- tySolve n1 (KindEffect :< TyFlat (Set.difference e2 l1)) -- TODO for all these differences, need to flatten?
          else
            contradiction
        else
          defer
    | null (extract unis t1 ++ extract unis t2) -> contradiction
    | otherwise                     -> defer

  Specialises _ (_ :< QTyUni _) -> defer

  Specialises t q -> do
    t' <- ungeneralise Phantom q
    introduce [ Eq t t' ]

  Generalises _ _ -> defer

  _ -> contradiction

  where solved = return True
        tautology = solved
        defer = require d >> return False
        contradiction = throwError . CheckError . Contradiction $ d
        introduce cs = requireAll (map (d `implies`) cs) >> return True
        swap = case constraint d of t1 `Eq` t2 -> progress d{ constraint = t2 `Eq` t1 }

        snake :: Set (Typed Type) -> Maybe (Name, Set (Typed Type))
        snake es = case Set.toList es of
          ((_ :< TyUni n):es) -> if null (concatMap (extract unis) es) then Just (n, Set.fromList es) else Nothing
          _                   -> Nothing

        literals :: Set (Typed Type) -> Bool
        literals es = null (concatMap (extract unis) (Set.toList es))

qTySolve :: Name -> Typed QType -> Praxis Bool
qTySolve n q = do
  let f :: Typed QType -> Praxis (Typed QType)
      f = pure . subs (\n' -> if n == n' then Just q else Nothing)
  over (our . qTySol) ((n, q):)
  modify our (pseudoTraverse f)
  modify tEnv (traverse f)
  reuse n
  return True

tySolve :: Name -> Typed Type -> Praxis Bool
tySolve n p = do
  let f :: Typed Type -> Praxis (Typed Type)
      f = tyGenSub (\n' -> if n == n' then Just p else Nothing)
  over (our . tySol) ((n, p):)
  modify our (pseudoTraverse f)
  modify tEnv (traverse (pseudoTraverse f))
  reuse n
  return True


tcmap :: (Typed Type -> Typed Type) -> Typed (Const Constraint) -> Typed (Const Constraint)
tcmap f c = over value f' (over (annotation . origin) f' c)
  where f' c = case c of
    Eq t1 t2 -> Eq (f t1) (f t2)
    -- TODO FIXME

qcmap :: (Typed QType -> Typed QType) -> Typed (Const Constraint) -> Typed (Const Constraint)
qcmap = undefined
-- qcmap = over value f' (over (annotation . origin) f' c)


tsolve :: Name -> Type TypeCheck -> Praxis Bool
tsolve n t = do
  let f :: forall a. Recursive a => Typed a -> Typed a
      f = sub (\t' -> case t' of { TyUni n' | n == n' -> Just t; _ -> Nothing })
  our . tsol %= ((n, t):)
  our . constraints %= fmap (cmap f)
  our . staging %= fmap (cmap f)
  our . axioms %= fmap (cmap f)
  -- tEnv %= over traverse f
  reuse n
  return True

qsolve :: Name -> QType TypeCheck -> Praxis Bool
qsolve n q = do
  let f :: forall a. Recursive a => Typed a -> Typed a
      f = sub (\q' -> case q' of { QTyUni n' | n == n' -> Just q; _ -> Nothing })
  our . qsol %= ((n, q):)
  our . constraints %= fmap (qcmap f)
  our . staging %= fmap (qcmap f)
  our . axioms %= fmap (qcmap f)
  -- tEnv %= over traverse f
  reuse n
  return True

-}
