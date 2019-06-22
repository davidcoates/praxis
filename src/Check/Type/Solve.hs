{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Check.Type.Solve
  ( solve
  ) where

import           Check.Type.Error
import           Check.Type.Require
import           Check.Type.System
import           Common
import           Env.TEnv            (ungeneralise)
import           Introspect
import           Praxis
import           Record
import           Stage
import           Term

import           Control.Applicative (liftA2)
import           Data.List           (nub, sort)
import           Data.Maybe          (fromMaybe)
import           Data.Set            (Set, union)
import qualified Data.Set            as Set

solve :: Praxis [(Name, Type TypeAnn)]
solve = save stage $ save our $ do
  stage .= TypeCheck Solve
  solve'
  use (our . sol)

data State = Cold
           | Warm
           | Done

solve' :: Praxis State
solve' = spin progress `chain` stuck where
  chain :: Praxis State -> Praxis State -> Praxis State
  chain p1 p2 = p1 >>= \case
    Cold -> p2
    Warm -> solve'
    Done -> return Done
  stuck = do
    cs <- (nub . sort) <$> use (our . constraints)
    output $ separate "\n\n" cs
    throw Stuck

spin :: (Typed TypeConstraint -> Praxis Bool) -> Praxis State
spin solve = use (our . constraints) <&> (nub . sort) >>= \case
  [] -> return Done
  cs -> do
    our . constraints .= []
    our . staging .= cs
    warm <- loop
    return $ if warm then Warm else Cold
  where
    loop = use (our . staging) >>= \case
        []     -> return False
        (c:cs) -> (our . staging .= cs) >> liftA2 (||) (solve c) loop

unis = extract (only f)
 where f (TyUni n) = [n]
       f _         = []

-- TODO use sets here?
classes :: [Name] -> [Typed TypeConstraint] -> Maybe [Typed Type]
classes ns cs = (\f -> concat <$> mapM f cs) $ \d -> case view value d of
  Class t     -> let ns' = unis t in if all (`elem` ns) ns' then Just [t] else if any (`elem` ns') ns then Nothing else Just []
  TEq t1 t2   -> if any (`elem` (unis t1 ++ unis t2)) ns then Nothing else Just []

progress :: Typed TypeConstraint -> Praxis Bool
progress d = case view value d of

  Class (k1 :< TyApply (k2 :< TyCon "Share") (a :< p)) -> case p of -- TODO Need instance solver!
    TyFun _ _                   -> tautology
    TyUni _                     -> defer
    TyCon n | n `elem` ["Int", "Char", "Bool"] -> tautology
    TyRecord r                  -> introduce (map ((\t -> Class (k1 :< TyApply (k2 :< TyCon "Share") t)). snd) (Record.toList r))
    _                           -> contradiction

  TEq t1 t2 | t1 == t2 -> tautology

  TEq (_ :< TyUni x) t -> if x `elem` unis t then contradiction else x ~> view value t
  TEq _ (_ :< TyUni _) -> swap

  TEq (_ :< TyApply n1 t1) (_ :< TyApply n2 t2) | n1 == n2  -> introduce [ TEq t1 t2 ]

  TEq (_ :< TyRecord r1) (_ :< TyRecord r2) | sort (keys r1) == sort (keys r2) ->
    let values = map snd . Record.toCanonicalList in introduce (zipWith TEq (values r1) (values r2)) -- TODO create zipRecord or some such

  TEq (_ :< TyFun t1 t2) (_ :< TyFun s1 s2) -> introduce [ TEq t1 s1, TEq t2 s2 ]

  TEq t1@(_ :< TyFlat e1) t2@(_ :< TyFlat e2)
    | e1 > e2 -> swap
    | [_ :< TyUni n] <- Set.toList e1 -> if n `elem` unis t2 then defer else n ~> view value t2
    | []             <- Set.toList e1 -> let empty (_ :< TyUni n) = n ~> TyFlat Set.empty
                                             empty _              = contradiction
                                         in foldr (\a b -> empty a >> b) solved e2
    | Just ((n1, l1), (n2, l2)) <- liftA2 (,) (snake e1) (snake e2) ->
        if n1 == n2 then do
          a <- freshUniT
          n1 ~> TyFlat (Set.unions [Set.singleton a, Set.difference l2 l1, Set.difference l1 l2])
        else
          n1 ~> TyFlat (Set.union (Set.difference l2 l1) (Set.singleton (TyUni n2 `as` phantom KindType)))
    | Just (n1, l1) <- snake e1 ->
        if literals e2 then
          if Set.isSubsetOf l1 e2 then
            defer
            -- FIXME This isn't correct! We could add any subset of l1 to n1
            -- solve n1 (TyFlat (Set.difference e2 l1)) -- TODO for all these differences, need to flatten?
          else
            contradiction
        else
          defer
    | null (unis t1 ++ unis t2) -> contradiction
    | otherwise                     -> defer

  _ -> contradiction

  where solved = return True
        tautology = solved
        defer = require d >> return False
        contradiction = throw (Contradiction d)
        introduce cs = requires (map (d `implies`) cs) >> return True
        swap = case view value d of t1 `TEq` t2 -> progress (set value (t2 `TEq` t1) d)

        snake :: Set (Typed Type) -> Maybe (Name, Set (Typed Type))
        snake es = case Set.toList es of
          ((_ :< TyUni n):es) -> if null (concatMap unis es) then Just (n, Set.fromList es) else Nothing
          _                   -> Nothing

        literals :: Set (Typed Type) -> Bool
        literals es = null (concatMap unis (Set.toList es))

smap :: (forall a. Recursive a => Typed a -> Typed a) -> Praxis ()
smap f = do
  let lower :: (Typed Type -> Typed Type) -> Type TypeAnn -> Type TypeAnn
      lower f = view value . f . (`as` phantom KindType)
  our . sol %= fmap (over second (lower f))
  our . constraints %= fmap f
  our . staging %= fmap f
  our . axioms %= fmap f
  tEnv %= over traverse f

(~>) :: Name -> Type TypeAnn -> Praxis Bool
(~>) n t = do
  smap $ sub (\case { TyUni n' | n == n' -> Just t; _ -> Nothing })
  our . sol %= ((n, t):)
  reuse n
  return True

