{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Check.Type.Check
  ( check
  ) where

import           Data.Set            (Set)
import qualified Data.Set            as Set

import           Check.Type.Generate as Generate
import           Check.Type.Require
import           Check.Type.Solve    as Solve
import           Check.Type.System
import           Common
import           Introspect
import           Praxis
import           Stage
import           Term

check :: Term a => Annotated a -> Praxis (Annotated a)
check x = save stage $ do
  stage .= TypeCheck Warmup
  our .= initialSystem
  x <- Generate.run x
  sol <- Solve.run >>= tryDefault x
  let tys   = view tySol sol
      tyOps = view tyOpSol sol
  let f :: forall a. Term a => a -> Maybe a
      f x = case witness :: I a of
        IType -> case x of {   TyUni n   ->  lookup n  tys; _ -> Nothing }
        ITyOp -> case x of { TyOpUni _ n -> lookup n tyOps; _ -> Nothing }
        _     -> Nothing
  r <- normalise (sub f x)
  display r `ifFlag` debug
  return r


deepTyUnis :: forall a. Term a => Annotated a -> Set Name
deepTyUnis = deepExtract (embedMonoid f) where
  f = \case
    TyUni n -> Set.singleton n
    _       -> Set.empty

deepTyOpUnis :: forall a. Term a => Annotated a -> Set Name
deepTyOpUnis = deepExtract (embedMonoid f) where
  f = \case
    TyOpUni _ n -> Set.singleton n
    _           -> Set.empty

tryDefault :: Term a => Annotated a -> Solution -> Praxis Solution
tryDefault x sol = do

  -- TODO could just be a warning, and default to ()?
  let freeTys = deepTyUnis   x `Set.difference` Set.fromList (map fst (view tySol sol))
  when (not (null freeTys)) $ throwAt (view source x) $ "underdetermined type: " <> quote (pretty (Set.elemAt 0 freeTys))

  let freeTyOps = deepTyOpUnis x `Set.difference` Set.fromList (map fst (view tyOpSol sol))
  flip mapM_ freeTyOps $ \tyOp -> do
    warnAt (view source x) $ "undertermined type operator: " <> quote (pretty tyOp) <> ", defaulting to &"

  let defaultTyOp n = do
        r <- freshTyOpRef
        return (n, view value r)

  defaultedTyOps <- mapM defaultTyOp (Set.toList freeTyOps)

  let sol' = over tyOpSol (++ defaultedTyOps) sol

  return sol'
