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
    output $ separate "\n\n" cs
    throw Stuck

spin :: Praxis State
spin = use (our . constraints) <&> (nub . sort) >>= \case
  [] -> return Done
  cs -> do
    our . constraints .= []
    our . staging .= cs
    warm <- loop
    return $ if warm then Warm else Cold
  where
    loop = use (our . staging) >>= \case
        []     -> return False
        (c:cs) -> (our . staging .= cs) >> liftA2 (||) (smap eval >> progress c) loop

unis = extract (embedMonoid f)
 where f (TyUni n) = [n]
       f _         = []

-- TODO use sets here?
classes :: [Name] -> [Annotated TypeConstraint] -> Maybe [Annotated Type]
classes ns cs = (\f -> concat <$> mapM f cs) $ \d -> case view value d of
  Class t     -> let ns' = unis t in if all (`elem` ns) ns' then Just [t] else if any (`elem` ns') ns then Nothing else Just []
  TEq t1 t2   -> if any (`elem` (unis t1 ++ unis t2)) ns then Nothing else Just []

data Resolution = Proven
                | Disproven { open :: Bool }
                | Unproven { antecedents :: [Annotated TypeConstraint], trivial :: Bool }
  deriving Show

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
resolve c = case view value c of

  Share t -> do
    s <- shareImpl c
    a <- shareImpl (phantom (Affine t))
    case (s, a) of
      (Unproven _ _, _)     -> defer
      (_, Unproven _ _)     -> defer
      (Proven, Proven)      -> throw (AffineInconsistency t)
      (Proven, Disproven _) -> return Proven
      (Disproven o, _)      -> return (Disproven o)

  Affine t -> do
    s <- shareImpl (phantom (Share t))
    a <- shareImpl c
    case (s, a) of
      (Unproven _ _, _)     -> defer
      (_, Unproven _ _)     -> defer
      (Proven, Proven)      -> throw (AffineInconsistency t)
      (Proven, Disproven _) -> return Proven
      (Disproven o, _)      -> return (Disproven o)

  TEq t1 t2 | t1 == t2 -> tautology

  TEq (_ :< TyUni x) t -> if x `elem` unis t then contradiction else x `is` view value t >> solved
  TEq _ (_ :< TyUni _) -> swap

  TEq (_ :< TyApply n1 t1) (_ :< TyApply n2 t2) | n1 == n2 -> introduce [ TEq t1 t2 ]

  TEq (_ :< TyRecord r1) (_ :< TyRecord r2) | sort (keys r1) == sort (keys r2) ->
    let values = map snd . Record.toCanonicalList in introduce (zipWith TEq (values r1) (values r2)) -- TODO create zipRecord or some such

  TEq (_ :< TyFun t1 t2) (_ :< TyFun s1 s2) -> introduce [ TEq t1 s1, TEq t2 s2 ]

  TEq (_ :< TyOp (_ :< TyOpUni n1) t1) (_ :< TyOp (_ :< TyOpUni n2) t2) | n1 == n2 -> introduce [ TEq t1 t2 ]

  TEq (_ :< TyOp (_ :< op) t1) t2 -> do
    s1 <- resolve (phantom (Share t1))
    s2 <- resolve (phantom (Share t2))
    case (op, truth s1, truth s2, viewFree t2) of
      (TyOpUni _, _, Just True, True)        -> introduce [ TEq t1 t2 ]
      (TyOpUni n, Just False, Just False, _) -> n `isView` False >> introduce [ TEq t1 t2 ]
      (TyOpUni n, Just False, Just True,  _) -> n `isView` True >> solved
      _ -> defer

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

    shareImpl :: Annotated TypeConstraint -> Praxis Resolution
    shareImpl c = case view value t of

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

      TyVar n -> do
        axs <- fmap (view value) <$> use (our . axioms)
        resolved ((if p then Share else Affine) t `elem` axs)

      _ -> defer

      where
        (p, t) = case view value c of
          Share t  -> (True, t)
          Affine t -> (False, t)

        share t = c `implies` (if p then Share else Affine) t

        defer = return $ Unproven { antecedents = [ c ], trivial = True }


    viewFree :: Annotated Type -> Bool
    viewFree t = case view value t of
      TyUni _ -> False
      TyOp (_ :< op) t -> case op of
        TyOpBang  -> False
        TyOpUni _ -> False
        TyOpId    -> viewFree t
      _ -> True


smap :: (forall a. Recursive a => Annotated a -> Praxis (Annotated a)) -> Praxis ()
smap f = do
  let lower :: (Annotated Type -> Praxis (Annotated Type)) -> Type -> Praxis Type
      lower f x = view value <$> f (x `as` phantom KindType)
  our . sol %%= traverse (second (lower f))
  our . constraints %%= traverse f
  our . staging %%= traverse f
  our . axioms %%= traverse f
  tEnv %%= traverse f
  return ()

isView :: Name -> Bool -> Praxis ()
isView n b = do
  let op = if b then TyOpBang else TyOpId
  smap $ pure . sub (\case { TyOpUni n' | n == n' -> Just op; _ -> Nothing })
  our . ops %= ((n, op):)
  return ()

is :: Name -> Type -> Praxis ()
is n t = do
  smap $ pure . sub (\case { TyUni n' | n == n' -> Just t; _ -> Nothing })
  our . sol %= ((n, t):)
  reuse n
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
