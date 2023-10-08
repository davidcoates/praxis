{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Check.Kind.Check
  ( check
  ) where

import           Data.Set            (Set)
import qualified Data.Set            as Set

import           Check.Kind.Generate as Generate
import           Check.Kind.Require
import           Check.Kind.Solve    as Solve
import           Check.Kind.System
import           Common
import           Introspect
import           Praxis
import           Stage
import           Term

check :: Term a => Annotated a -> Praxis (Annotated a)
check term = save stage $ do
  stage .= KindCheck Warmup
  our .= initialSystem
  term <- Generate.run term
  kindSol <- Solve.run >>= tryDefault term
  let term' = sub (embedSub (\k -> case k of { KindUni n -> lookup n kindSol; _ -> Nothing })) term
  display term' `ifFlag` debug
  return term'


deepKindUnis :: forall a. Term a => Annotated a -> Set Name
deepKindUnis = deepExtract (embedMonoid f) where
  f = \case
    KindUni n -> Set.singleton n
    _         -> Set.empty

tryDefault :: Term a => Annotated a -> [(Name, Kind)] -> Praxis [(Name, Kind)]
tryDefault x kindSol = do

  -- TODO could just be a warning, and default to Type?
  let freeKinds = deepKindUnis   x `Set.difference` Set.fromList (map fst kindSol)
  when (not (null freeKinds)) $ throwAt (view source x) $ "underdetermined kind: " <> quote (pretty (Set.elemAt 0 freeKinds))

  return kindSol
