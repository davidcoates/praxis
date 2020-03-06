{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Check.Type.Solve
  ( solve
  , eval
  ) where

import           Check.Type.Error
import           Check.Type.Require
import           Check.Type.System
import           Common
import           Introspect
import           Praxis
import           Pretty
import           Record
import           Stage               hiding (Unknown)
import           Term

import           Control.Applicative (liftA2)
import           Data.List           (foldl', nub, sort)
import           Data.Maybe          (fromMaybe)
import           Data.Set            (Set, union)
import qualified Data.Set            as Set
import           Data.Traversable    (forM)

solve :: Praxis ([(Name, Type)], [(Name, TyOp)])
solve = save stage $ save our $ do
  stage .= TypeCheck Solve
  solve'
  ts <- use (our . sol)
  ops <- use (our . ops)
  return (ts, ops)

data State = Cold
           | Warm
           | Done

solve' :: Praxis State
solve' = spin `chain` stuck where
  chain :: Praxis State -> Praxis State -> Praxis State
  chain p1 p2 = p1 >>= \case
    Cold -> p2
    Warm -> solve'
    Done -> return Done
  stuck = do
    cs <- (nub . sort) <$> use (our . constraints)
    display (separate "\n\n" cs) `ifFlag` debug
    throw Stuck

spin :: Praxis State
spin = use (our . constraints) <&> (nub . sort) >>= \case
  [] -> return Done
  cs -> do
    our . constraints .= []
    our . staging .= cs
    warm <- loop
    cs <- (nub . sort) <$> use (our . constraints)
    display (separate "\n\n" cs) `ifFlag` debug
    return $ if warm then Warm else Cold
  where
    loop = use (our . staging) >>= \case
        []     -> return False
        (c:cs) -> (our . staging .= cs) >> liftA2 (||) (progress c) loop

unis = extract (embedMonoid f)
 where f (TyUni n) = [n]
       f _         = []

data Resolution = Proven
                | Disproven { open :: Bool }
                | Unproven { antecedents :: [Annotated TypeConstraint], trivial :: Bool }

(&&&) :: Resolution -> Resolution -> Resolution
(&&&) = curry $ \case
  (Proven, r)      -> r
  (r, Proven)      -> r
  (Disproven o, _) -> Disproven o
  (_, Disproven o) -> Disproven o
  (r, s)           -> Unproven { antecedents = antecedents r ++ antecedents s, trivial = trivial r || trivial s }

(|||) :: Resolution -> Resolution -> Resolution
(|||) = curry $ \case
  (Disproven _, r) -> r
  (r, Disproven _) -> r
  (Proven, _)      -> Proven
  (_, Proven)      -> Proven
  (r, s)           -> Unproven { antecedents = antecedents r ++ antecedents s, trivial = trivial r || trivial s }

truth :: Resolution -> Maybe Bool
truth = \case
  Proven      -> Just True
  Disproven _ -> Just False
  _           -> Nothing

untrivialise :: Resolution -> Resolution
untrivialise r = case r of
  Unproven { trivial = True } -> r{ trivial = False }
  _                           -> r

progress :: Annotated TypeConstraint -> Praxis Bool
progress c = resolve c >>= \case
  Proven                            -> return True
  Disproven _                       -> throw (Contradiction c)
  Unproven { antecedents, trivial } -> requires antecedents >> return (not trivial)

resolve :: Annotated TypeConstraint -> Praxis Resolution
resolve c = checkAxioms c $ case view value c of

  Share t -> shareImpl c

  Affine t -> shareImpl c

  TEq t1 t2 | t1 == t2 -> tautology

  TEq (_ :< TyUni x) t -> if x `elem` unis t then contradiction else x `is` view value t >> solved -- Note: Occurs check here
  TEq _ (_ :< TyUni _) -> swap

  TEq (_ :< TyApply n1 t1) (_ :< TyApply n2 t2) | n1 == n2 -> introduce [ TEq t1 t2 ]

  TEq (_ :< TyRecord r1) (_ :< TyRecord r2) | sort (keys r1) == sort (keys r2) ->
    let values = map snd . Record.toCanonicalList in introduce (zipWith TEq (values r1) (values r2)) -- TODO create zipRecord or some such

  TEq (_ :< TyFun t1 t2) (_ :< TyFun s1 s2) -> introduce [ TEq t1 s1, TEq t2 s2 ]

  TEq (_ :< TyOp op1 t1) t2 -> do
    s1 <- resolve (phantom (Share t1))
    s2 <- resolve (phantom (Share t2))
    case (view value op1, truth s1, truth s2) of
      (TyOpUni n, Just False, Just True) -> n `isOp` TyOpBang
      (TyOpUni n, _, Just False)         -> n `isOp` TyOpId
      (_, _, Just True) | viewFree t2    -> introduce [ TEq t1 t2 ]
      _  | TyOp op2 t2 <- view value t2  -> do
          s2 <- resolve (phantom (Share t2))
          case (truth s1, truth s2) of
            (Just False, Just False) -> case (view value op1, view value op2) of
              (TyOpUni n1, TyOpUni n2) -> if n1 == n2 then introduce [ TEq t1 t2 ] else n1 `isOp` TyOpUni n2
              (TyOpUni n1, op)         -> n1 `isOp` op
              (op, TyOpUni n2)         -> n2 `isOp` op
              (TyOpVar n1, TyOpVar n2) -> if n1 == n2 then introduce [ TEq t1 t2 ] else contradiction
              (TyOpBang, TyOpBang)     -> introduce [ TEq t1 t2 ]
              _                        -> contradiction
            _ -> defer
      _                                  -> defer

  TEq _ (_ :< TyOp _ _) -> swap

  _ -> contradiction


  where
    tautology :: Praxis Resolution
    tautology = return Proven

    solved = tautology

    contradiction :: Praxis Resolution
    contradiction = return $ Disproven { open = False }

    introduce :: [TypeConstraint] -> Praxis Resolution
    introduce cs = return $ Unproven { antecedents = map (c `implies`) cs, trivial = False }

    defer :: Praxis Resolution
    defer = return $ Unproven { antecedents = [ c ], trivial = True }

    resolved :: Bool -> Praxis Resolution
    resolved True  = tautology
    resolved False = contradiction

    swap = case view value c of t1 `TEq` t2 -> resolve (set value (t2 `TEq` t1) c)

    checkAxioms :: Annotated TypeConstraint -> Praxis Resolution -> Praxis Resolution
    checkAxioms c r = do
      isAxiom <- (c `elem`) <$> use (our . axioms)
      if isAxiom then solved else r

    shareImpl :: Annotated TypeConstraint -> Praxis Resolution
    shareImpl c = checkAxioms c $ case view value t of

      TyOp (_ :< op) t'
        | TyOpBang  <- op -> resolved p
        | TyOpUni _ <- op -> do
          r <- resolve (share t')
          case truth r of
            Just p' | p == p' -> resolved (not p')
            _                 -> defer

      TyFun _ _  -> resolved p

      TyRecord r -> untrivialise <$> (foldl' (if p then (&&&) else (|||)) (if p then Proven else Disproven { open = False }) <$> forM r (resolve . share))

      TyCon n
        | n `elem` ["Int", "Char", "Bool"] -> resolved p

      -- FIXME make this general!
      TyApply (_ :< TyCon "List") _ -> resolved (not p)

      _ -> defer

      where
        (p, t) = case view value c of
          Share t  -> (True, t)
          Affine t -> (False, t)

        share t = c `implies` (if p then Share else Affine) t

        defer = return $ Unproven { antecedents = [ c ], trivial = True }


    viewFree :: Annotated Type -> Bool
    viewFree t = case view value t of
      TyUni _  -> False
      TyOp _ _ -> False
      _        -> True

    isOp :: Name -> TyOp -> Praxis Resolution
    isOp n op = do
      let f :: forall a. Recursive a => Annotated a -> Praxis (Annotated a)
          f  = eval . sub (embedSub (\case { TyOpUni n' | n == n' -> Just op; _ -> Nothing }))
      smap f
      our . ops %= ((n, op):)
      c' <- f c
      return $ Unproven { antecedents = [ c' ], trivial = False }

    is :: Name -> Type -> Praxis ()
    is n t = do
      smap $ eval . sub (embedSub (\case { TyUni n' | n == n' -> Just t; _ -> Nothing }))
      our . sol %= ((n, t):)
      reuse n
      return ()


smap :: (forall a. Recursive a => Annotated a -> Praxis (Annotated a)) -> Praxis ()
smap f = do
  let lower :: Recursive a => (Annotated a -> Praxis (Annotated a)) -> a -> Praxis a
      lower f x = view value <$> f (phantom x)
  our . sol %%= traverse (second (lower f))
  our . ops %%= traverse (second (lower f))
  our . constraints %%= traverse f
  our . staging %%= traverse f
  our . axioms %%= traverse f
  tEnv %%= traverse f
  return ()

eval :: forall a. Recursive a => Annotated a -> Praxis (Annotated a)
eval x = introspect (embedVisit f) x where
  f :: Annotated Type -> Visit Praxis () Type
  f (a :< t) = case t of
    TyOp (_ :< TyOpId) t -> Resolve (view value <$> eval t)
    TyOp (a :< op) t -> Resolve $ do
      t' <- eval t
      r <- resolve (phantom (Share t'))
      return $ case r of
        Proven -> view value t'
        _      -> TyOp (a :< op) t'
    _ -> skip
