{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types        #-}
{-# LANGUAGE TypeFamilies      #-}

module Check.Solve
  ( tautology
  , solved
  , contradiction
  , intro
  , defer
  , resolved

  , Resolution(..)
  , Solver(..)
  , (<|>)
  , solve
  , solveProp
  ) where

import           Common
import           Introspect
import           Praxis
import           Print
import           Term

import           Check.Require

type Resolution a = Praxis (Maybe (Prop a))

tautology :: Resolution a
tautology = return (Just Top)

solved :: Resolution a
solved = tautology

contradiction :: Resolution a
contradiction = return (Just Bottom)

intro :: [a] -> Resolution a
intro = return . Just . all' . map Exactly where
  all' [p]    = p
  all' (p:ps) = p `And` all' ps

defer :: Resolution a
defer = return Nothing

resolved :: Bool -> Resolution a
resolved b = if b then solved else contradiction

type Solver a b = a -> Resolution b

(<|>) :: Solver a a -> Solver a a -> Solver a a
s1 <|> s2 = \a -> do
  r1 <- s1 a
  case r1 of
    Just _  -> return r1
    Nothing -> s2 a

solve :: (Annotation (Prop a) ~ Derivation (Prop a), Term a, Term (Prop a)) => Lens' PraxisState [Annotated (Prop a)] -> Solver a a -> Praxis ()
solve constraints solveConstraint = use constraints >>= (\cs -> solve' cs [] False) where
  solve' []     [] _ = return ()
  solve' []     rs w = do
    when (not w) (display (separate "\n\n" rs <> "\n") >> throw ("failed to solve constraints" :: String))
    solve' rs [] False
  solve' (p:ps) rs w = do
    constraints .= (ps ++ rs)
    r <- solveProp constraints solveConstraint (view value p)
    cs' <- use constraints
    let ps' = take (length ps) cs'
        rs' = drop (length ps) cs'
    case r of
      Just Top    -> solve' ps' rs' (w || True)
      Just Bottom -> throw $ "found contradiction " <> pretty p
      Just p'     -> solve' ps' ((p `impliesProp` p') : rs') (w || True)
      Nothing     -> solve' ps' (p:rs') w

push :: Lens' PraxisState [Annotated (Prop a)] -> Prop a -> Praxis ()
push constraints p = constraints %= (phantom p:)

pop :: Lens' PraxisState [Annotated (Prop a)] -> Praxis (Prop a)
pop constraints = do
  (p:ps) <- use constraints
  constraints .= ps
  return (view value p)

solveProp :: Lens' PraxisState [Annotated (Prop a)] -> Solver a a -> Solver (Prop a) a
solveProp constraints solveConstraint = \case

  Exactly c -> solveConstraint c

  p1 `And` p2 -> do

    -- push the subtree not being worked on to allow substitutions to be applied to them
    push constraints p2
    r1 <- solveProp constraints solveConstraint p1
    p2 <- pop constraints

    let normalise r p = case r of { Nothing -> p; Just r -> r }

    push constraints (r1 `normalise` p1)
    r2 <- solveProp constraints solveConstraint p2
    p1 <- pop constraints

    return $ case (r1, r2) of
      (Nothing, Nothing) -> Nothing
      _                  -> Just $ case (p1, r2 `normalise` p2) of
        (Bottom, _) -> Bottom
        (_, Bottom) -> Bottom
        (x,    Top) -> x
        (Top,    y) -> y
        (x,      y) -> x `And` y
