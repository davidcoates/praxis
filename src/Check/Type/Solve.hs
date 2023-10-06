{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Check.Type.Solve
  ( run
  , normalise
  ) where

import           Check.Error
import           Check.Solve
import           Check.Type.Require
import           Check.Type.System
import           Common
import           Introspect
import           Praxis
import           Stage               hiding (Unknown)
import           Term

import           Control.Applicative (liftA2)
import           Data.List           (foldl', nub, sort)
import           Data.Maybe          (fromMaybe)
import           Data.Set            (Set, union)
import qualified Data.Set            as Set
import           Data.Traversable    (forM)

run :: Praxis Solution
run = save stage $ save our $ do
  stage .= TypeCheck Solve
  solve (our . constraints) solveTy
  use (our . sol)

tyUnis :: forall a. Term a => Annotated a -> Set Name
tyUnis = extract (embedMonoid f) where
  f = \case
    TyUni n -> Set.singleton n
    _       -> Set.empty

tyOpUnis :: forall a. Term a => Annotated a -> Set Name
tyOpUnis = extract (embedMonoid f) where
  f = \case
    TyOpUni _ n -> Set.singleton n
    _           -> Set.empty

type TypeSolver = Solver TyConstraint TyConstraint

solveDeep :: TypeSolver -> TypeSolver
solveDeep s = \c -> do
  p <- s c
  case p of
    Nothing     -> return $ Nothing
    Just Top    -> return $ Just Top
    Just Bottom -> return $ Just Bottom
    Just p      -> solveProp (our . constraints) (solveDeep s) p


trySolveShare t = save our $ save tEnv $ solveDeep (trySolveShare') (Share t) where
  trySolveShare' = (solveFromAxioms <|>) $ \(Share t) -> case view value t of
    TyUnit                                   -> tautology
    TyFun _ _                                -> tautology
    TyPair a b                               -> intro [ Share a, Share b]
    TyVar _                                  -> contradiction
    TyCon _                                  -> contradiction
    TyApply (_ :< TyCon _) _                 -> contradiction
    TyApply (_ :< TyOp (_ :< TyOpRef _)) _   -> tautology
    TyApply (_ :< TyOp (_ :< TyOpVar _ _)) _ -> contradiction
    _                                        -> defer


solveTy :: TypeSolver
solveTy = (solveFromAxioms <|>) $ \c -> case c of

  Share t -> trySolveShare t

  TEq t1 t2 | t1 == t2 -> tautology

  TEq (_ :< TyUni x) t -> if x `Set.member` tyUnis t then contradiction else x `is` view value t -- Note: Occurs check here

  TEq t1 t2@(_ :< TyUni _) -> solveTy (t2 `TEq` t1) -- handle by the above case

  TEq (_ :< TyApply (_ :< TyCon n1) t1) (_ :< TyApply (_ :< TyCon n2) t2)
    | n1 == n2 -> intro [ TEq t1 t2 ]
    | otherwise -> contradiction

  TEq (_ :< TyPack s1 s2) (_ :< TyPack t1 t2) -> intro [ TEq s1 t1, TEq s2 t2 ]

  TEq (_ :< TyPair s1 s2) (_ :< TyPair t1 t2) -> intro [ TEq s1 t1, TEq s2 t2 ]

  TEq (_ :< TyFun t1 t2) (_ :< TyFun s1 s2) -> intro [ TEq t1 s1, TEq t2 s2 ]

  TEq t1@(_ :< TyApply (_ :< TyOp op1) t1') t2 -> intro [ TEq (stripOuterTyOps t1') (stripOuterTyOps t2), TOpEq t1 t2 ]

  TEq t1 t2@(_ :< TyApply (_:< TyOp _) _) -> solveTy (t2 `TEq` t1) -- handled by the above case

  TOpEq t1 t2 | outerTyOps t1 == outerTyOps t2 -> tautology

  TOpEq t1 t2 -> do
    r <- trySolveShare (stripOuterTyOps t1) -- stripOuterTyOps t1 == stripOuterTyOps t2
    case r of
      Just Bottom -> do
        let (ops1, ops2) = let f = Set.toList . outerTyOps in (f t1, f t2)
        case (if ops1 < ops2 then (ops1, ops2) else (ops2, ops1)) of
          ([], vs) -> do
            if all (\v -> case view value v of { TyOpUni _ _ -> True; _ -> False }) vs
            then mapM (\(_ :< TyOpUni _ n) -> n `isOp` TyOpId) vs >> solved
            else contradiction
          ([_ :< TyOpUni d1 n], [_ :< TyOpUni d2 m]) | d1 == d2 && n == m -> tautology
          ([_ :< TyOpUni d  n], [_ :< op]) -> n `isOp` op
          _ -> defer
      _ -> defer

  _ -> contradiction


solveFromAxioms :: TypeSolver
solveFromAxioms c = use (our . axioms) >>= (\as -> solveFromAxioms' as c) where
  -- TODO this is just an asum
  solveFromAxioms' :: [Axiom] -> TypeSolver
  solveFromAxioms' = \case
    []             -> (\c -> pure Nothing)
    ((Axiom a):as) -> (\c -> pure (a c)) <|> solveFromAxioms' as

-- Assumes the type is normalised
viewFree :: Annotated Type -> Bool
viewFree t = case view value t of
  TyUni _                 -> False
  TyApply (_ :< TyOp _) _ -> False
  _                       -> True

isOp :: Name -> TyOp -> Praxis (Maybe TyProp)
isOp n op = do
  our . sol . tyOpSol %= ((n, op):)
  simplifyAll
  solved

is :: Name -> Type -> Praxis (Maybe TyProp)
is n t = do
  our . sol . tySol %= ((n, t):)
  simplifyAll
  solved

simplify :: forall a. Term a => Annotated a -> Praxis (Annotated a)
simplify x = do
  tys <- use (our . sol . tySol)
  tyOps <- use (our . sol . tyOpSol)
  let simplify' :: forall a. Term a => a -> Maybe a
      simplify' x = case witness :: I a of {
        IType -> case x of { TyUni     n -> n `lookup`   tys; _ -> Nothing };
        ITyOp -> case x of { TyOpUni _ n -> n `lookup` tyOps; _ -> Nothing };
        _     -> Nothing}
  normalise (sub simplify' x)


simplifyAll :: Praxis ()
simplifyAll = do
  our . sol . tySol   %%= traverse (second (covalue simplify))
  our . sol . tyOpSol %%= traverse (second (covalue simplify))
  our . constraints %%= traverse simplify
  tEnv %%= traverse simplify


outerTyOps :: Annotated Type -> Set (Annotated TyOp)
outerTyOps t = case view value t of
  TyApply (_ :< TyOp op) t -> Set.insert op (outerTyOps t)
  _                        -> Set.empty

stripOuterTyOps :: Annotated Type -> Annotated Type
stripOuterTyOps t = case view value t of
  TyApply (_ :< TyOp _) t -> stripOuterTyOps t
  _                       -> t


simplifyOuterTyOps :: Annotated Type -> Annotated Type
simplifyOuterTyOps = simplifyOuterTyOps' [] where

  simplifyOuterTyOps' :: [TyOp] -> Annotated Type -> Annotated Type
  simplifyOuterTyOps' ops t = case view value t of

    TyApply o@(_ :< TyOp (_ :< op)) t' -> case op of
      TyOpId    -> simplifyOuterTyOps' ops t'
      TyOpRef _ -> set value (TyApply o (stripOuterTyOps t')) t
      _
        | op `elem` ops -> simplifyOuterTyOps' ops t'
        | otherwise     -> let t'' = simplifyOuterTyOps' (op:ops) t' in case view value t'' of
          TyApply (_ :< TyOp (_ :< TyOpRef r)) _ -> t''
          _ -> set value (TyApply o t'') t

    _ -> t


normalise :: forall a. Term a => Annotated a -> Praxis (Annotated a)
normalise x = introspect (embedVisit f) x where

  f :: Annotated Type -> Visit Praxis () Type
  f t = case view value t of

    TyApply (_ :< TyOp _) _ -> case simplifyOuterTyOps t of

      t@(_ :< TyApply o@(_ :< TyOp (_ :< op)) t') -> Resolve $ do
        r <- trySolveShare t'
        return $ case r of
          Just Top -> view value t'
          _        -> view value t

      t -> Resolve (view value <$> normalise t)

    _ -> skip
