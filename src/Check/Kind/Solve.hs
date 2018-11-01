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
import           Source
import           Stage
import           Tag
import           Type

import           Control.Applicative    (Const (..), liftA2)
import           Control.Monad.Identity (Identity (..))
import           Data.List              (nub, sort)
import           Data.Maybe             (fromMaybe)
import           Data.Set               (Set, union)
import qualified Data.Set               as Set
import           Prelude                hiding (log)

solve :: Praxis [(Name, Kind)]
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
            throwError (CheckError (KindError (Stuck)))

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

unis :: Kind -> [Name]
unis k = case k of
  KindUni n      -> [n]
  KindConstraint -> []
  KindEffect     -> []
  KindFun k1 k2  -> unis k1 ++ unis k2
  KindRecord r   -> concatMap (unis . snd) (toList r)
  KindType       -> []


progress :: Kinded KindConstraint -> Praxis Bool
progress c'@(d :< c) = case c of

  Eq k1 k2 | k1 == k2  -> tautology

  Eq (KindUni x) k -> if x `elem` unis k then contradiction else x ~> k
  Eq _ (KindUni _) -> swap

  Eq (KindRecord r1) (KindRecord r2) | sort (keys r1) == sort (keys r2) ->
    let values = map snd . Record.toCanonicalList in introduce (zipWith Eq (values r1) (values r2)) -- TODO create zipRecord or some such

  Eq (KindFun t1 t2) (KindFun t3 t4) -> introduce [ Eq t1 t3, Eq t2 t4 ]

  _ -> contradiction

  where solved = return True
        tautology = solved
        defer = require c' >> return False
        contradiction = throwError . CheckError . KindError . Contradiction $ c'
        introduce cs = requires (map (c' `implies`) cs) >> return True
        swap = case c of Eq k1 k2 -> progress (d :< Eq k2 k1)

ksub :: (Name -> Maybe Kind) -> Kind -> Kind
ksub f k = case k of
  KindUni n      -> fromMaybe k (f n)
  KindConstraint -> k
  KindEffect     -> k
  KindFun k1 k2  -> KindFun (ksub f k1) (ksub f k2)
  KindRecord r   -> KindRecord (fmap (ksub f) r)
  KindType       -> k

cmap :: (Kind -> Kind) -> Kinded KindConstraint -> Kinded KindConstraint
cmap f c = let f' (Eq k1 k2) = Eq (f k1) (f k2) in
  over value f' (over (annotation . antecedent) (cmap f <$>) c)

(~>) :: Name -> Kind -> Praxis Bool
(~>) n k = do
  let f :: Kind -> Kind
      f = ksub (\n' -> if n == n' then Just k else Nothing)
  our . sol %= ((n, k):)
  our . constraints %= fmap (cmap f)
  our . staging %= fmap (cmap f)
  our . axioms %= fmap (cmap f)
  kEnv %= over traverse f
  reuse n
  return True
