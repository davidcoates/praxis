{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Eval
  ( Evaluable(..)
  ) where

import           Common
import           Env
import           Praxis
import           Stage
import           Term
import           Value

import           Data.Monoid (Sum (..))
import           Prelude     hiding (exp, lookup)

class Evaluable a b | a -> b where
  eval' :: Annotated a -> Praxis b
  eval  :: Annotated a -> Praxis b
  eval e = save stage $ do
    stage .= Evaluate
    clearTerm `ifFlag` debug
    eval' e

instance Evaluable Program () where
  eval' = program

instance Evaluable Exp Value where
  eval' = exp

program :: Annotated Program -> Praxis ()
program (_ :< Program ds) = mapM_ decl ds

decl :: Annotated Decl -> Praxis ()
decl (a :< e) = case e of

  DeclVar n t e -> do
    e' <- expRec (Just n) e
    vEnv %= intro n e'

  _ -> return ()

stmt :: Annotated Stmt -> Praxis (Sum Int)
stmt (_ :< s) = case s of

  StmtDecl d -> decl d >> return (Sum 0)

  StmtExp e  -> exp e >> return (Sum 1)

rec :: Maybe Name -> Value -> Praxis ()
rec n v = case n of
  Just n  -> vEnv %= intro n v
  Nothing -> return ()

expRec :: Maybe Name -> Annotated Exp -> Praxis Value
expRec n (_ :< e) = case e of

  Apply f x -> do
    F f' <- exp f
    x' <- exp x
    f' x'

  Case e ps -> do
    v <- exp e
    cases v ps

  Cases ps -> do
    l <- use vEnv
    let e = F $ \v -> save vEnv $ do { vEnv .= l; rec n e; cases v ps }
    return e

  Con n -> do
    Just da <- daEnv `uses` lookup n
    let DataAltInfo _ _ args _ = view (annotation . just) da
    let f 0 = C n []
        f i = let C n vs = f (i-1) in F (\v -> return (C n (v:vs)))
    return (f (length args))

  Do ss -> do
    Sum i <- asum (map stmt (init ss))
    let _ :< StmtExp e = last ss
    v <- exp e
    vEnv %= elimN i
    return v

  If a b c -> do
    L (Bool a') <- exp a
    if a' then exp b else exp c

  Lambda p e -> do
    l <- use vEnv
    let f = F $ \v -> save vEnv $ do { vEnv .= l; rec n f; i <- forceBind v p; exp e }
    return f

  Lit l -> return (L l)

  Read _ e -> exp e

  Pair a b -> P <$> exp a <*> exp b

  Sig e _ -> exp e

  Unit -> pure U

  Var n -> do
    Just v <- vEnv `uses` lookup n
    return v

exp :: Annotated Exp -> Praxis Value
exp = expRec Nothing

cases :: Value -> [(Annotated Pat, Annotated Exp)] -> Praxis Value
cases x [] = error ("no matching pattern" ++ show x)
cases x ((p,e):ps) = case bind x p of
  Just c  -> do
    i <- c
    e' <- exp e
    vEnv %= elimN i
    return e'
  Nothing ->
    cases x ps

forceBind :: Value -> Annotated Pat -> Praxis Int
forceBind v p = case bind v p of Just i  -> i
                                 Nothing -> error "no matching pattern" -- TODO

binds :: [Value] -> [Annotated Pat] -> Maybe (Praxis Int)
binds vs ps = do
  cs <- sequence $ zipWith bind vs ps
  return (sum <$> sequence cs)

bind :: Value -> Annotated Pat -> Maybe (Praxis Int)
bind v (_ :< p) = case p of

  PatAt n p
    -> (\c -> do { vEnv %= intro n v; i <- c; return (i+1) }) <$> bind v p

  PatCon n ps | C m vs <- v
    -> if n == m then binds vs ps else Nothing

  PatHole
    -> Just (return 0)

  PatLit l | L l' <- v
    -> if l == l' then Just (return 0) else Nothing

  PatPair p q | P p' q' <- v
    -> binds [p', q'] [p, q]

  PatUnit
    -> Just (return 0)

  PatVar n
    -> Just $ vEnv %= intro n v >> return 1

  _
    -> Nothing
