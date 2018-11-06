{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Check.Type.Solve
  ( solve
  ) where

import           AST
import           Check.Error
import           Check.Type.Annotate
import           Check.Type.Constraint
import           Check.Type.Error
import           Check.Type.Require
import           Check.Type.System
import           Common
import           Env.TEnv               (ungeneralise)
import           Error
import           Introspect
import           Praxis
import           Record
import           Stage
import           Type

import           Control.Applicative    (Const (..), liftA2)
import           Control.Monad.Identity (Identity (..))
import           Data.List              (nub, sort)
import           Data.Maybe             (fromMaybe)
import           Data.Set               (Set, union)
import qualified Data.Set               as Set
import           Prelude                hiding (log)

solve :: Praxis ([(Name, Type TypeCheck)], [(Name, QType TypeCheck)])
solve = save stage $ save our $ do
  stage .= TypeCheck Solve
  solve'
  t <- use (our . tsol)
  q <- use (our . qsol)
  return (t, q)

throwTypeError = throwError . CheckError . TypeError

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
            throwTypeError Stuck

spin :: (Typed TypeConstraint -> Praxis Bool) -> Praxis State
spin solve = do
  cs <- (nub . sort) <$> use (our . constraints)
  case cs of
    [] -> return Done
    _  -> do
      our . constraints .= []
      our . staging .= cs
      warm <- loop
      return $ if warm then Warm else Cold
  where
    loop = do
      cs <- use (our . staging)
      case cs of
        []     -> return False
        (c:cs) -> (our . staging .= cs) >> liftA2 (||) (solve c) loop

unis = extract (only f)
 where f (TyUni n) = [n]
       f _         = []

generalise :: Typed TypeConstraint -> Praxis Bool
generalise d = do
  ds <- liftA2 (++) (use (our . constraints)) (use (our . staging))
  case view value d of
    Generalises (_ :< QTyUni n) t -> generalise' ds n t
    Generalises _               _ -> error "unreachable?"
    _                             -> defer
  where
    defer = require d >> return False
    generalise' :: [Typed TypeConstraint] -> Name -> Typed Type -> Praxis Bool
    generalise' ds n t = case classes (unis t) ds of
      Nothing -> defer
      Just ts -> qsolve n (generaliseType ts t)

generaliseType :: [Typed Type] -> Typed Type -> QType TypeCheck
generaliseType ts (a :< t) = case us of
  [] -> Mono (a :< t)
  _  -> undefined -- TODO For each uni in t, find an annotated kind. Use this to build up [(Name, Kind)]
  where us = unis (a :< t)
        vs = map (:[]) ['a'..]
        f u = (`lookup` zip us vs)

-- TODO use sets here?
classes :: [Name] -> [Typed TypeConstraint] -> Maybe [Typed Type]
classes ns cs = (\f -> concat <$> mapM f cs) $ \d -> case view value d of
  Class t         -> let ns' = unis t in if all (`elem` ns) ns' then Just [t] else if any (`elem` ns') ns then Nothing else Just []
  Eq t1 t2    -> if any (`elem` (unis t1 ++ unis t2)) ns then Nothing else Just []
  Generalises q t -> Just [] -- TODO not sure about these
  Specialises t q -> Just []


progress :: Typed TypeConstraint -> Praxis Bool
progress d = case view value d of

  Class (k1 :< TyApply (k2 :< TyCon "Share") (a :< p)) -> case p of -- TODO Need instance solver!
    TyApply (_ :< TyCon "->") _ -> tautology
    TyUni _                     -> defer
    TyCon n | n `elem` ["Int", "Char", "Bool"] -> tautology
    TyRecord r                  -> introduce (map ((\t -> Class (k1 :< TyApply (k2 :< TyCon "Share") t)). snd) (Record.toList r))
    _                           -> contradiction

  Eq t1 t2 | t1 == t2 -> tautology

  Eq (_ :< TyUni x) t -> if x `elem` unis t then contradiction else tsolve x (view value t)
  Eq _ (_ :< TyUni _) -> swap

  Eq (_ :< TyApply n1 t1) (_ :< TyApply n2 t2) | n1 == n2  -> introduce [ Eq t1 t2 ]

  Eq (_ :< TyPack r1) (_ :< TyPack r2) | sort (keys r1) == sort (keys r2) ->
    let values = map snd . Record.toCanonicalList in introduce (zipWith Eq (values r1) (values r2)) -- TODO create zipRecord or some such

  Eq (_ :< TyRecord r1) (_ :< TyRecord r2) | sort (keys r1) == sort (keys r2) ->
    let values = map snd . Record.toCanonicalList in introduce (zipWith Eq (values r1) (values r2)) -- TODO create zipRecord or some such

  Eq (_ :< TyApply n1 t1) (_ :< TyApply n2 t2) | n1 == n2  -> introduce [ Eq t1 t2 ]

  Eq t1@(_ :< TyFlat e1) t2@(_ :< TyFlat e2)
    | e1 > e2 -> swap
    | [_ :< TyUni n] <- Set.toList e1 -> if n `elem` unis t2 then defer else tsolve n (view value t2)
    | []             <- Set.toList e1 -> let empty (_ :< TyUni n) = tsolve n (TyFlat Set.empty)
                                             empty _              = contradiction
                                         in foldr (\a b -> empty a >> b) solved e2
    | Just ((n1, l1), (n2, l2)) <- liftA2 (,) (snake e1) (snake e2) ->
        if n1 == n2 then do
          a <- freshUniT
          tsolve n1 (TyFlat (Set.unions [Set.singleton a, Set.difference l2 l1, Set.difference l1 l2]))
        else
          tsolve n1 (TyFlat (Set.union (Set.difference l2 l1) (Set.singleton ((Phantom, ()) :< TyUni n2))))
    | Just (n1, l1) <- snake e1 ->
        if literals e2 then
          if Set.isSubsetOf l1 e2 then
            defer
            -- FIXME This isn't correct! We could add any subset of l1 to n1
            -- tsolve n1 (TyFlat (Set.difference e2 l1)) -- TODO for all these differences, need to flatten?
          else
            contradiction
        else
          defer
    | null (unis t1 ++ unis t2) -> contradiction
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
        contradiction = throwTypeError (Contradiction d)
        introduce cs = requires (map (d `implies`) cs) >> return True
        swap = case view value d of t1 `Eq` t2 -> progress (set value (t2 `Eq` t1) d)

        snake :: Set (Typed Type) -> Maybe (Name, Set (Typed Type))
        snake es = case Set.toList es of
          ((_ :< TyUni n):es) -> if null (concatMap unis es) then Just (n, Set.fromList es) else Nothing
          _                   -> Nothing

        literals :: Set (Typed Type) -> Bool
        literals es = null (concatMap unis (Set.toList es))

smap :: (forall a. Recursive a => Typed a -> Typed a) -> Praxis ()
smap f = do
  let lower :: forall a. (Recursive a, Annotation TypeCheck a ~ ()) => (Typed a -> Typed a) -> a TypeCheck -> a TypeCheck
      lower f = view value . f . ((Phantom, ()) :<)
  our . qsol %= fmap (over second (lower f))
  our . tsol %= fmap (over second (lower f))
  our . constraints %= fmap f
  our . staging %= fmap f
  our . axioms %= fmap f
  tEnv %= over traverse f

tsolve :: Name -> Type TypeCheck -> Praxis Bool
tsolve n t = do
  smap $ sub (\t' -> case t' of { TyUni n' | n == n' -> Just t; _ -> Nothing })
  our . tsol %= ((n, t):)
  reuse n
  return True

qsolve :: Name -> QType TypeCheck -> Praxis Bool
qsolve n q = do
  smap $ sub (\q' -> case q' of { QTyUni n' | n == n' -> Just q; _ -> Nothing })
  our . qsol %= ((n, q):)
  reuse n
  return True

