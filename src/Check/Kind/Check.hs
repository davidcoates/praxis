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
check x = save stage $ do
  stage .= KindCheck Warmup
  our .= initialSystem
  x <- Generate.run x
  ks <- Solve.run >>= tryDefault x
  let r = sub (embedSub (\k -> case k of { KindUni n -> lookup n ks; _ -> Nothing })) x
  display r `ifFlag` debug
  return r


deepKindUnis :: forall a. Term a => Annotated a -> Set Name
deepKindUnis = deepExtract (embedMonoid f) where
  f = \case
    KindUni n -> Set.singleton n
    _         -> Set.empty

tryDefault :: Term a => Annotated a -> [(Name, Kind)] -> Praxis [(Name, Kind)]
tryDefault x ks = do

  -- TODO could just be a warning, and default to Type?
  let freeKinds = deepKindUnis   x `Set.difference` Set.fromList (map fst ks)
  when (not (null freeKinds)) $ throwAt (view source x) $ "underdetermined kind: " <> quote (pretty (Set.elemAt 0 freeKinds))

  return ks
