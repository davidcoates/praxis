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
import           Introspect
import           Praxis
import           Pretty
import           Record
import           Stage
import           Term

import           Data.List          (nub, sort)
import           Data.Maybe         (fromMaybe)
import           Data.Set           (Set, union)
import qualified Data.Set           as Set

solve :: Praxis [(Name, Kind)]
solve = save stage $ save our $ do
  stage .= KindCheck Solve
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
    display (separate "\n\n" cs) `ifFlag` debug
    throw Stuck

-- TODO reduce duplication with Type Solve spin
spin :: (Annotated KindConstraint -> Praxis Bool) -> Praxis State
spin solve = use (our . constraints) <&> (nub . sort) >>= \case
  [] -> return Done
  cs -> do
    our . constraints .= []
    our . staging .= cs
    warm <- loop
    return $ if warm then Warm else Cold
  where
    loop = do
      use (our . staging) >>= \case
        []     -> return False
        (c:cs) -> (our . staging .= cs) >> liftA2 (||) (solve c) loop

unis = extract (embedMonoid f) where
  f = \case
    KindUni n      -> [n]
    KindConstraint -> []
    KindFun a b    -> unis a ++ unis b
    KindType       -> []
-- TODO find some way of combining traverseM and traverseA and use that here

progress :: Annotated KindConstraint -> Praxis Bool
progress d = case view value d of

  KEq k1 k2 | k1 == k2  -> tautology

  KEq (_ :< KindUni x) k -> if x `elem` unis k then contradiction else x `is` (view value k) -- Note: Occurs check here
  KEq _ (_ :< KindUni _) -> swap

  KEq (_ :< KindFun t1 t2) (_ :< KindFun t3 t4) -> introduce [ KEq t1 t3, KEq t2 t4 ]

  _ -> contradiction

  where
    solved = return True
    tautology = solved
    defer = require d >> return False
    contradiction = throw (Contradiction d)
    introduce cs = requires (map (d `implies`) cs) >> return True
    swap = case view value d of t1 `KEq` t2 -> progress (set value (t2 `KEq` t1) d)

    is :: Name -> Kind -> Praxis Bool
    is n k = do
      smap $ sub (embedSub (\case { KindUni n' | n == n' -> Just k; _ -> Nothing }))
      our . sol %= ((n, k):)
      reuse n
      return True

smap :: (forall a. Recursive a => Annotated a -> Annotated a) -> Praxis ()
smap f = do
  let lower :: (Annotated Kind -> Annotated Kind) -> Kind -> Kind
      lower f = view value . f . phantom
  our . sol %= fmap (over second (lower f))
  our . constraints %= fmap f
  our . staging %= fmap f
  our . axioms %= fmap f
  kEnv %= over traverse f
