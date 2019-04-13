{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Check.Kind.Solve
  ( solve
  ) where

import           AST
import           Check.Error
import           Check.Kind.Annotate
import           Check.Kind.Constraint
import           Check.Kind.Error
import           Check.Kind.Require
import           Check.Kind.System
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

solve :: Praxis [(Name, Kind KindCheck)]
solve = save stage $ save our $ do
  stage .= KindCheck Solve
  solve'
  use (our . sol)

data State = Cold
           | Warm
           | Done

throwKindError = throwError . CheckError . KindError

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
            throwKindError Stuck

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

  Eq k1 k2 | k1 == k2  -> tautology

  Eq (_ :< KindUni x) k -> if x `elem` unis k then contradiction else x ~> (view value k)
  Eq _ (_ :< KindUni _) -> swap

  Eq (_ :< KindRecord r1) (_ :< KindRecord r2) | sort (keys r1) == sort (keys r2) ->
    let values = map snd . Record.toCanonicalList in introduce (zipWith Eq (values r1) (values r2)) -- TODO create zipRecord or some such

  Eq (_ :< KindFun t1 t2) (_ :< KindFun t3 t4) -> introduce [ Eq t1 t3, Eq t2 t4 ]

  _ -> contradiction

  where solved = return True
        tautology = solved
        defer = require d >> return False
        contradiction = throwKindError (Contradiction d)
        introduce cs = requires (map (d `implies`) cs) >> return True
        swap = case view value d of t1 `Eq` t2 -> progress (set value (t2 `Eq` t1) d)

smap :: (forall a. Recursive a => Kinded a -> Kinded a) -> Praxis ()
smap f = do
  let lower :: forall a. (Recursive a, Annotation KindCheck a ~ ()) => (Kinded a -> Kinded a) -> a KindCheck -> a KindCheck
      lower f = view value . f . ((Phantom, ()) :<)
  our . sol %= fmap (over second (lower f))
  our . constraints %= fmap f
  our . staging %= fmap f
  our . axioms %= fmap f
  kEnv %= over traverse f

(~>) :: Name -> Kind KindCheck -> Praxis Bool
(~>) n k = do
  smap $ sub (\k' -> case k' of { KindUni n' | n == n' -> Just k; _ -> Nothing })
  our . sol %= ((n, k):)
  reuse n
  return True
