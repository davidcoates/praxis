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

run :: Praxis ([(Name, Type)], [(Name, TyOp)])
run = save stage $ save our $ do
  stage .= TypeCheck Solve
  solve (our . constraints) solveTy
  ts <- use (our . sol)
  ops <- use (our . ops)
  return (ts, ops)

tyUnis :: forall a. Term a => Annotated a -> Set Name
tyUnis = extract (embedMonoid f) where
  f = \case
    TyUni n -> Set.singleton n
    _       -> Set.empty

tyOpUnis :: forall a. Term a => Annotated a -> Set Name
tyOpUnis = extract (embedMonoid f) where
  f = \case
    TyOpUni n -> Set.singleton n
    _         -> Set.empty

type TypeSolver = Solver TypeConstraint TypeConstraint

solveDeep :: TypeSolver -> TypeSolver
solveDeep s = \c -> do
  p <- s c
  case p of
    Nothing     -> return $ Nothing
    Just Top    -> return $ Just Top
    Just Bottom -> return $ Just Bottom
    Just p      -> solveProp (our . constraints) (solveDeep s) p

trySolveShare :: Solver (Annotated Type) TypeConstraint
trySolveShare t = save our $ save tEnv $ solveDeep (trySolveShare') (Share t) where
  trySolveShare' = (solveFromAxioms <|>) $ \(Share t) -> case view value t of
    TyUnit                 -> tautology
    TyFun _ _              -> tautology
    TyPair a b             -> intro [ Share a, Share b]
    TyOp (_ :< TyOpBang) _ -> tautology
    TyCon _ _              -> contradiction
    _                      -> defer

solveTy :: TypeSolver
solveTy = (solveFromAxioms <|>) $ \c -> case c of

  Share t -> case view value t of
      TyUnit                  -> tautology
      TyFun _ _               -> tautology
      TyPair a b              -> intro [ Share a, Share b]
      TyOp (_ :< TyOpBang) _  -> tautology
      TyOp (_ :< TyOpVar _) _ -> contradiction
      TyVar _                 -> contradiction
      TyCon _ _               -> contradiction -- not in axioms, so can be sure the type is not affine
      _                       -> defer

  TEq t1 t2 | t1 == t2 -> tautology

  TEq (_ :< TyUni x) t -> if x `Set.member` tyUnis t then contradiction else x `is` view value t -- Note: Occurs check here

  TEq c1 c2@(_ :< TyUni _) -> solveTy (c2 `TEq` c1) -- handle by the above case

  TEq (_ :< TyCon n1 (Just t1)) (_ :< TyCon n2 (Just t2)) | n1 == n2 -> intro [ TEq t1 t2 ]

  TEq (_ :< TyPack s1 s2) (_ :< TyPack t1 t2) -> intro [ TEq s1 t1, TEq s2 t2 ]

  TEq (_ :< TyPair s1 s2) (_ :< TyPair t1 t2) -> intro [ TEq s1 t1, TEq s2 t2 ]

  TEq (_ :< TyFun t1 t2) (_ :< TyFun s1 s2) -> intro [ TEq t1 s1, TEq t2 s2 ]

  TEq (_ :< TyOp (_ :< TyOpVar n1) t1) (_ :< TyOp (_ :< TyOpVar n2) t2) | n1 == n2 -> intro [ TEq t1 t2 ]

  TEq (_ :< TyOp op1 t1) t2 -> do
    s1 <- trySolveShare t1
    s2 <- trySolveShare t2
    case (view value op1, s1, s2) of
      (TyOpUni n, Just Bottom,    Just Top) -> n `isOp` TyOpBang
      (TyOpUni n,           _, Just Bottom) -> n `isOp` TyOpId
      (TyOpBang,            _, Just Bottom) -> contradiction
      (_,                   _,    Just Top) | viewFree t2 -> intro [ TEq t1 t2 ]
      _                                     | TyOp op2 t2 <- view value t2  -> do
          s2 <- trySolveShare t2
          case (s1, s2) of
            (Just Bottom, Just Bottom) -> case (view value op1, view value op2) of
              (TyOpUni n1, TyOpUni n2) -> if n1 == n2 then intro [ TEq t1 t2 ] else n1 `isOp` TyOpUni n2
              (TyOpUni n1, op)         -> n1 `isOp` op
              (op, TyOpUni n2)         -> n2 `isOp` op
              (TyOpBang, TyOpBang)     -> intro [ TEq t1 t2 ]
              _                        -> contradiction
            _ -> defer
      _                                  -> defer

  TEq c1 c2@(_ :< TyOp _ _) -> solveTy (c2 `TEq` c1) -- handled by the above case

  TOpEq c1 c2 | c1 == c2 -> tautology

  TOpEq (_ :< TyOpUni x) o -> if x `Set.member` tyOpUnis o then contradiction else x `isOp` view value o -- Note: Occurs check here

  TOpEq c1 c2@(_ :< TyOpUni _) -> solveTy (c2 `TOpEq` c1) -- handled by the above case

  _ -> contradiction


solveFromAxioms :: TypeSolver
solveFromAxioms c = use (our . axioms) >>= (\as -> solveFromAxioms' as c) where
  -- TODO this is just an asum
  solveFromAxioms' :: [Axiom] -> TypeSolver
  solveFromAxioms' = \case
    []             -> (\c -> pure Nothing)
    ((Axiom a):as) -> (\c -> pure (a c)) <|> solveFromAxioms' as

viewFree :: Annotated Type -> Bool
viewFree t = case view value t of
  TyUni _  -> False
  TyOp _ _ -> False
  _        -> True

isOp :: Name -> TyOp -> Praxis (Maybe TypeProp)
isOp n op = do
  our . ops %= ((n, op):)
  simplifyAll
  solved

is :: Name -> Type -> Praxis (Maybe TypeProp)
is n t = do
  our . sol %= ((n, t):)
  simplifyAll
  solved

simplify :: forall a. Term a => Annotated a -> Praxis (Annotated a)
simplify x = do
  tys <- use (our . sol)
  tyOps <- use (our . ops)
  let simplify' :: forall a. Term a => a -> Maybe a
      simplify' x = case witness :: I a of {
        IType -> case x of { TyUni   n -> n `lookup`   tys; _ -> Nothing };
        ITyOp -> case x of { TyOpUni n -> n `lookup` tyOps; _ -> Nothing };
        _     -> Nothing}
  normalise (sub simplify' x)


simplifyAll :: Praxis ()
simplifyAll = do
  our . sol %%= traverse (second (covalue simplify))
  our . ops %%= traverse (second (covalue simplify))
  our . constraints %%= traverse simplify
  tEnv %%= traverse simplify


normalise :: forall a. Term a => Annotated a -> Praxis (Annotated a)
normalise x = introspect (embedVisit f) x where
  f :: Annotated Type -> Visit Praxis () Type
  f (a :< t) = case t of
    TyOp (_ :< TyOpId) t -> Resolve (view value <$> normalise t)
    TyOp (a :< op) t -> Resolve $ do
      t' <- normalise t
      r <- solveTy (Share t')
      return $ case r of
        Just Top -> view value t'
        _        -> TyOp (a :< op) t'
    _ -> skip
