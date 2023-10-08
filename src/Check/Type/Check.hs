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
check term = save stage $ do
  stage .= TypeCheck Warmup
  our .= initialSystem
  term <- Generate.run term
  sol <- Solve.run >>= tryDefault term
  let tys   = view tySol sol
      tyOps = view tyOpSol sol
  let f :: forall a. Term a => a -> Maybe a
      f term = case witness :: I a of
        IType -> case term of {   TyUni n   ->  lookup n  tys; _ -> Nothing }
        ITyOp -> case term of { TyOpUni _ n -> lookup n tyOps; _ -> Nothing }
        _     -> Nothing
  term' <- normalise (sub f term)
  display term' `ifFlag` debug
  return term'


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
tryDefault term@((src, _) :< _) sol = do

  -- TODO could just be a warning, and default to ()?
  let freeTys = deepTyUnis term `Set.difference` Set.fromList (map fst (view tySol sol))
  when (not (null freeTys)) $ throwAt src $ "underdetermined type: " <> quote (pretty (Set.elemAt 0 freeTys))

  let freeTyOps = deepTyOpUnis term `Set.difference` Set.fromList (map fst (view tyOpSol sol))
  flip mapM_ freeTyOps $ \tyOp -> do
    warnAt src $ "underdetermined type operator: " <> quote (pretty tyOp) <> ", defaulting to &"

  let defaultTyOp n = do
        r <- freshTyOpRef
        return (n, view value r)

  defaultedTyOps <- mapM defaultTyOp (Set.toList freeTyOps)

  return $ over tyOpSol (++ defaultedTyOps) sol
