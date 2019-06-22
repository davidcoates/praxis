{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Eval
  ( Evaluable(..)
  ) where

import           Common
import           Env.VEnv    (VEnv, elim, elimN, intro)
import qualified Env.VEnv    as VEnv (fromList, lookup)
import           Praxis
import           Record
import           Term
import           Value

import           Data.Monoid (Sum (..))
import           Prelude     hiding (exp)

class Evaluable a b | a -> b where
  eval' :: Typed a -> Praxis b
  eval  :: Typed a -> Praxis b
  eval e = save stage $ do
    stage .= Evaluate
    clear
    eval' e

instance Evaluable Program () where
  eval' = program

instance Evaluable Exp Value where
  eval' = exp

program :: Typed Program -> Praxis ()
program (_ :< Program ds) = mapM_ decl ds

decl :: Typed Decl -> Praxis ()
decl (a :< e) = case e of

  DeclVar n t e -> do
    e' <- exp e
    intro n e'

  _ -> return ()

stmt :: Typed Stmt -> Praxis (Sum Int)
stmt (_ :< s) = case s of

  StmtDecl d -> decl d >> return (Sum 0)

  StmtExp e  -> exp e >> return (Sum 1)


exp :: Typed Exp -> Praxis Value
exp (_ :< e) = case e of

  Apply f x -> do
    F f' <- exp f
    x' <- exp x
    f' x'

  Case e ps -> do
    v <- exp e
    cases v ps

  Cases ps -> return $ F $ \v -> cases v ps

  Do ss -> do
    Sum i <- asum (map stmt (init ss))
    let _ :< StmtExp e = last ss
    v <- exp e
    elimN i
    return v

  If a b c -> do
    L (Bool a') <- exp a
    if a' then exp b else exp c

  Lambda p e -> return $ F $ \v -> do
    i <- forceBind v p
    e' <- exp e
    elimN i
    return e'

  Lit l -> return (L l)

  Read _ e -> exp e

  Record r -> do
    x <- mapM exp r
    return (R x)

  Sig e _ -> exp e

  Var n -> do
    Just v <- VEnv.lookup n
    return v


cases :: Value -> [(Typed Pat, Typed Exp)] -> Praxis Value
cases x [] = error ("no matching pattern" ++ show x)
cases x ((p,e):ps) = case bind x p of
  Just c  -> do
    i <- c
    e' <- exp e
    elimN i
    return e'
  Nothing ->
    cases x ps

forceBind :: Value -> Typed Pat -> Praxis Int
forceBind v p = case bind v p of Just i  -> i
                                 Nothing -> error "no matching pattern" -- TODO

bind :: Value -> Typed Pat -> Maybe (Praxis Int)
bind v (_ :< p) = case p of

  PatAt n p
    -> (\c -> do { intro n v; i <- c; return (i+1) }) <$> bind v p

  PatHole
    -> Just (return 0)

  PatLit l | L l' <- v
    -> if l == l' then Just (return 0) else Nothing

  PatRecord r | R r' <- v
    -> do
    let vs = map snd $ Record.toCanonicalList r'
        ps = map snd $ Record.toCanonicalList r
    cs <- sequence $ map (\(a, b) -> bind a b) (zip vs ps)
    return (sum <$> sequence cs)

  PatVar n
    -> Just $ intro n v >> return 1

  _
    -> Nothing
