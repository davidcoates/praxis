{-# LANGUAGE OverloadedStrings    #-}
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


run :: Term a => Annotated a -> Praxis (Annotated a)
run term = save stage $ save our $ do
  stage .= TypeCheck Solve
  solve (our . constraints) solveTy
  tryDefault term
  simplify term

deepTyUnis :: forall a. Term a => Annotated a -> Set Name
deepTyUnis = deepExtract (embedMonoid f) where
  f = \case
    TyUni n -> Set.singleton n
    _       -> Set.empty

deepViewUnis :: forall a. Term a => Annotated a -> Set Name
deepViewUnis = deepExtract (embedMonoid f) where
  f = \case
    ViewUni _ n -> Set.singleton n
    _           -> Set.empty

tryDefault :: Term a => Annotated a -> Praxis ()
tryDefault term@((src, _) :< _) = do

  tys <- use (our . sol . tySol)
  views <- use (our . sol . viewSol)

  -- TODO could just be a warning, and default to ()?
  let freeTys = deepTyUnis term `Set.difference` Set.fromList (map fst tys)
  when (not (null freeTys)) $ throwAt src $ "underdetermined type: " <> quote (pretty (Set.elemAt 0 freeTys))

  let freeViews = deepViewUnis term `Set.difference` Set.fromList (map fst views)
  flip mapM_ freeViews $ \view -> do
    warnAt src $ "underdetermined view: " <> quote (pretty view) <> ", defaulting to &"

  let defaultView n = do
        r <- freshViewRef
        n `isOp` (view value r)

  mapM defaultView (Set.toList freeViews)
  return ()



tyUnis :: forall a. Term a => Annotated a -> Set Name
tyUnis = extract (embedMonoid f) where
  f = \case
    TyUni n -> Set.singleton n
    _       -> Set.empty

viewUnis :: forall a. Term a => Annotated a -> Set Name
viewUnis = extract (embedMonoid f) where
  f = \case
    ViewUni _ n -> Set.singleton n
    _           -> Set.empty

viewRefs :: forall a. Term a => Annotated a -> Set Name
viewRefs = extract (embedMonoid f) where
  f = \case
    ViewRef n -> Set.singleton n
    _         -> Set.empty

type TypeSolver = Solver TyConstraint TyConstraint

solveDeep :: TypeSolver -> TypeSolver
solveDeep s = \c -> do
  p <- s c
  case p of
    Nothing     -> return $ Nothing
    Just Top    -> return $ Just Top
    Just Bottom -> return $ Just Bottom
    Just p      -> solveProp (our . constraints) (solveDeep s) p


trySolveCopy t = save our $ save tEnv $ solveDeep (trySolveCopy') (Copy t) where
  trySolveCopy' = (solveFromAxioms <|>) $ \(Copy t) -> case view value t of
    TyUnit                                     -> tautology
    TyFun _ _                                  -> tautology
    TyPair a b                                 -> intro [ Copy a, Copy b ]
    TyVar _                                    -> contradiction
    TyCon _                                    -> contradiction
    TyApply (_ :< TyCon _) _                   -> contradiction
    TyApply (_ :< View (_ :< ViewRef _)) _     -> tautology
    TyApply (_ :< View (_ :< ViewUni Ref _)) _ -> tautology
    TyApply (_ :< View (_ :< ViewVar Ref _)) _ -> tautology
    TyApply (_ :< View (_ :< ViewVar _ _)) a   -> intro [ Copy a ]
    TyApply (_ :< View (_ :< ViewValue)) a     -> intro [ Copy a ]
    _                                          -> defer


solveTy :: TypeSolver
solveTy = (solveFromAxioms <|>) $ \c -> case c of

  Copy t -> trySolveCopy t

  TEq t1 t2 | t1 == t2 -> tautology

  TEq (_ :< TyUni x) t -> if x `Set.member` tyUnis t then contradiction else x `is` view value t -- Note: Occurs check here

  TEq t1 t2@(_ :< TyUni _) -> solveTy (t2 `TEq` t1) -- handle by the above case

  TEq (_ :< TyApply (_ :< TyCon n1) t1) (_ :< TyApply (_ :< TyCon n2) t2)
    | n1 == n2 -> intro [ TEq t1 t2 ]
    | otherwise -> contradiction

  TEq (_ :< TyPack s1 s2) (_ :< TyPack t1 t2) -> intro [ TEq s1 t1, TEq s2 t2 ]

  TEq (_ :< TyPair s1 s2) (_ :< TyPair t1 t2) -> intro [ TEq s1 t1, TEq s2 t2 ]

  TEq (_ :< TyFun t1 t2) (_ :< TyFun s1 s2) -> intro [ TEq t1 s1, TEq t2 s2 ]

  TEq t1@(_ :< TyApply (_ :< View op1) t1') t2 -> intro [ TEq (stripOuterViews t1') (stripOuterViews t2), TOpEq t1 t2 ]

  TEq t1 t2@(_ :< TyApply (_:< View _) _) -> solveTy (t2 `TEq` t1) -- handled by the above case

  TOpEq t1 t2 | outerViews t1 == outerViews t2 -> tautology

  TOpEq t1 t2 -> do
    r <- trySolveCopy (stripOuterViews t1) -- stripOuterViews t1 == stripOuterViews t2
    case r of
      Just Bottom -> do
        let (ops1, ops2) = let f = Set.toList . outerViews in (f t1, f t2)
        case (if ops1 < ops2 then (ops1, ops2) else (ops2, ops1)) of
          ([], vs) -> do
            if all (\v -> case view value v of { ViewUni RefOrValue _ -> True; _ -> False }) vs
            then mapM (\(_ :< ViewUni _ n) -> n `isOp` ViewValue) vs >> solved
            else contradiction
          -- Note: RefOrValue < Ref
          ([_ :< ViewUni RefOrValue n], [_ :< op])             -> n `isOp` op
          ([_ :< ViewUni Ref n], [_ :< ViewValue])             -> contradiction
          ([_ :< ViewUni Ref n], [_ :< ViewVar RefOrValue _])  -> contradiction
          ([_ :< ViewUni Ref n], [_ :< op@(ViewVar Ref _)]) -> n `isOp` op
          ([_ :< ViewUni Ref n], [_ :< op@(ViewRef _)])     -> n `isOp` op
          ([_ :< ViewUni Ref n], [_ :< op@(ViewUni Ref m)]) -> n `isOp` op
          _ -> defer
      _ -> defer

  RefFree refName t
    | refName `Set.member` viewRefs t -> contradiction
    | Set.null (tyUnis t) && Set.null (viewUnis t) -> tautology
    | otherwise -> defer

  _ -> contradiction


solveFromAxioms :: TypeSolver
solveFromAxioms c = use (our . axioms) >>= (\as -> solveFromAxioms' as c) where
  -- TODO this is just an asum
  solveFromAxioms' :: [Axiom] -> TypeSolver
  solveFromAxioms' = \case
    []             -> (\c -> pure Nothing)
    ((Axiom a):as) -> (\c -> pure (a c)) <|> solveFromAxioms' as

-- Assumes the type is normalised
-- FIXME unused
viewFree :: Annotated Type -> Bool
viewFree t = case view value t of
  TyUni _                 -> False
  TyApply (_ :< View _) _ -> False
  _                       -> True

isOp :: Name -> View -> Praxis (Maybe TyProp)
isOp n op = do
  our . sol . viewSol %= ((n, op):)
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
  views <- use (our . sol . viewSol)
  let simplify' :: forall a. Term a => a -> Maybe a
      simplify' x = case witness :: I a of {
        IType -> case x of { TyUni     n -> n `lookup`   tys; _ -> Nothing };
        IView -> case x of { ViewUni _ n -> n `lookup` views; _ -> Nothing };
        _     -> Nothing}
  normalise (sub simplify' x)


simplifyAll :: Praxis ()
simplifyAll = do
  our . sol . tySol   %%= traverse (second (covalue simplify))
  our . sol . viewSol %%= traverse (second (covalue simplify))
  our . constraints %%= traverse simplify
  tEnv %%= traverse simplify


outerViews :: Annotated Type -> Set (Annotated View)
outerViews ty = case view value ty of
  TyApply (_ :< View op) ty -> Set.insert op (outerViews ty)
  _                         -> Set.empty

stripOuterViews :: Annotated Type -> Annotated Type
stripOuterViews ty = case view value ty of
  TyApply (_ :< View _) ty -> stripOuterViews ty
  _                        -> ty


simplifyOuterViews :: Annotated Type -> Annotated Type
simplifyOuterViews = simplifyOuterViews' [] where

  simplifyOuterViews' :: [View] -> Annotated Type -> Annotated Type
  simplifyOuterViews' ops (ann :< ty) = case ty of

    TyApply f@(_ :< View (_ :< op)) innerTy -> case op of

      ViewValue    -> simplifyOuterViews' ops innerTy

      _

        | op `elem` ops -> simplifyOuterViews' ops innerTy

        | otherwise     -> ann :< TyApply f (simplifyOuterViews' (op:ops) innerTy)

    _ -> ann :< ty


normalise :: forall a. Term a => Annotated a -> Praxis (Annotated a)
normalise = introspect (embedVisit f) where

  f :: Annotated Type -> Visit Praxis () Type
  f ty = case view value ty of

    TyApply (_ :< View _) _ -> case simplifyOuterViews ty of

      ty@(_ :< TyApply (_ :< View _) innerTy) -> Resolve $ do
        -- The view can be safely stripped if the /* stripped */ type is copyable.
        --
        -- E.g. we can not strip &a from &a &b List Int (because List Int is not copyable)
        -- But we can strip &a from &a &b Int, and then &b from &b Int.
        canStripOps <- trySolveCopy (stripOuterViews innerTy)
        case canStripOps of
          Just Top -> view value <$> normalise (stripOuterViews innerTy)
          _        -> return (view value ty)

      ty -> Resolve (view value <$> normalise ty)

    _ -> skip
