{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Check.Kind.Solve
  ( solve
  ) where

import           Check.Kind.Error
import           Check.Kind.Require
import           Check.Kind.System
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

solve :: Praxis [(Name, Kind KindAnn)]
solve = save stage $ save our $ do
  stage .= KindCheck Solve
  solve'
  use (our . sol)

data State = Cold
           | Warm
           | Done

solve' :: Praxis State
solve' = spin progress `chain` stuck
    where chain :: Praxis State -> Praxis State -> Praxis State
          chain p1 p2 = p1 >>= \s -> case s of
            Cold -> p2
            Warm -> solve'
            Done -> return Done
          stuck = do
            -- FIXME
            -- cs <- get (our . constraints)
            -- logList Normal cs
            throw Stuck

-- TODO reduce duplication with Type Solve spin
spin :: (Kinded KindConstraint -> Praxis Bool) -> Praxis State
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

unis = extract (only f) where
  f k = case k of
    KindUni n      -> [n]
    KindConstraint -> []
    KindFun a b    -> unis a ++ unis b
    KindRecord a   -> concatMap (unis . snd) (toList a)
    KindType       -> []
-- TODO find some way of combining traverseM and traverseA and use that here

progress :: Kinded KindConstraint -> Praxis Bool
progress d = case view value d of

  KEq k1 k2 | k1 == k2  -> tautology

  KEq (_ :< KindUni x) k -> if x `elem` unis k then contradiction else x ~> (view value k)
  KEq _ (_ :< KindUni _) -> swap

  KEq (_ :< KindRecord r1) (_ :< KindRecord r2) | sort (keys r1) == sort (keys r2) ->
    let values = map snd . Record.toCanonicalList in introduce (zipWith KEq (values r1) (values r2)) -- TODO create zipRecord or some such

  KEq (_ :< KindFun t1 t2) (_ :< KindFun t3 t4) -> introduce [ KEq t1 t3, KEq t2 t4 ]

  _ -> contradiction

  where solved = return True
        tautology = solved
        defer = require d >> return False
        contradiction = throw (Contradiction d)
        introduce cs = requires (map (d `implies`) cs) >> return True
        swap = case view value d of t1 `KEq` t2 -> progress (set value (t2 `KEq` t1) d)

smap :: (forall a. Recursive a => Kinded a -> Kinded a) -> Praxis ()
smap f = do
  let lower :: (Kinded Kind -> Kinded Kind) -> Kind KindAnn -> Kind KindAnn
      lower f = view value . f . phantom
  our . sol %= fmap (over second (lower f))
  our . constraints %= fmap f
  our . staging %= fmap f
  our . axioms %= fmap f
  kEnv %= over traverse f

(~>) :: Name -> Kind KindAnn -> Praxis Bool
(~>) n k = do
  smap $ sub (\k' -> case k' of { KindUni n' | n == n' -> Just k; _ -> Nothing })
  our . sol %= ((n, k):)
  reuse n
  return True
