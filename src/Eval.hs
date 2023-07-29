{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE OverloadedStrings      #-}

module Eval
  ( Evaluable(..)
  ) where

import           Check.Type.Generate (recursive)
import           Common
import           Env
import           Praxis
import           Stage
import           Term
import           Value               (Value)
import qualified Value

import           Control.Monad.Fix   (mfix)
import           Data.Array.IO
import           Data.List           (partition)
import           Data.Maybe          (mapMaybe)
import           Prelude             hiding (exp, lookup)

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
program (_ :< Program ds) = decls ds

-- A helper for decls, irrefutably matching the [b] argument
irrefMapM :: Monad m => ((a, b) -> m c) -> [a] -> [b] -> m [c]
irrefMapM f as bs = case as of
  []     -> return []
  (a:as) -> case bs of
    ~(b:bs) -> do
      c <- f (a, b)
      cs <- irrefMapM f as bs
      return (c : cs)


decls :: [Annotated Decl] -> Praxis ()
decls ds = do

  -- Only variable declartions (values / functions) can be evaluated, so we only need to consider DeclVar
  let declVar :: Annotated Decl -> Maybe (Name, Annotated Exp)
      declVar = \case
        (_ :< DeclVar n _ e) -> Just (n, e)
        _ -> Nothing
      ds' = mapMaybe declVar ds

  -- Split values into potentially recursive & definitely not recursive
  let (rec, nonRec) = partition (recursive . snd) ds'

  -- Evaluate non-recursive values. This is simple as we can simply evaluate each one in turn.
  mapM_ (\(n, e) -> do { v <- exp e; vEnv %= intro n v }) nonRec

  -- Evaluate recursive values. This is not simple as we have to allow each value to see the evaluation of all other values (including itself).
  -- Leverage mfix to find the fixpoint (where vs stands for the list of evaluations).
  mfix $ \vs -> do
    -- Evaluate each of the values in turn, with all of the evaluations in the environment
    -- Note: The use of irrefMapM here is essential to avoid divergence of mfix.
    irrefMapM (\(n, v) -> vEnv %= intro n v) (map fst rec) vs
    mapM exp (map snd rec)

  return ()


stmt :: Annotated Stmt -> Praxis ()
stmt (_ :< s) = case s of

  StmtBind b -> bind b

  StmtExp e  -> exp e >> return ()


exp :: Annotated Exp -> Praxis Value
exp ((s, _) :< e) = case e of

  Apply f x -> do
    Value.Fun f' <- exp f
    x' <- exp x
    f' x'

  Case e ps -> do
    v <- exp e
    cases s v ps

  Cases ps -> do
    l <- use vEnv
    return $ Value.Fun $ \v -> save vEnv $ do { vEnv .= l; cases s v ps }

  Con n -> do
    Just da <- daEnv `uses` lookup n
    let DataConInfo { argType } = view (annotation . just) da
    return $ case argType of
      Nothing -> Value.Con n Nothing
      Just _  -> Value.Fun (\v -> return $ Value.Con n (Just v))

  Do ss -> save vEnv $ do
    mapM stmt (init ss)
    let _ :< StmtExp e = last ss
    v <- exp e
    return v

  If a b c -> do
    Value.Bool a' <- exp a
    if a' then exp b else exp c

  Lambda p e -> do
    l <- use vEnv
    return $ Value.Fun $ \v -> save vEnv $ do { vEnv .= l; forceBind s v p; exp e }

  Let b x -> save vEnv $ do
    bind b
    exp x

  Lit l -> case l of
    Bool b   -> pure $ Value.Bool b
    Char c   -> pure $ Value.Char c
    Int  i   -> pure $ Value.Int  i
    String s -> Value.Array <$> Value.fromString s

  Read _ e -> exp e

  Pair a b -> Value.Pair <$> exp a <*> exp b

  Sig e _ -> exp e

  Switch alts -> switch s alts

  Term.Unit -> return Value.Unit

  Var n -> do
    m <- vEnv `uses` lookup n
    case m of
       Just v  -> return v
       Nothing -> throwAt s ("unknown variable " <> quote (pretty n))

  Where x ys -> save vEnv $ do
    decls ys
    exp x


switch :: Source -> [(Annotated Exp, Annotated Exp)] -> Praxis Value
switch s [] = throwAt s ("inexhaustive switch" :: String)
switch s ((c,e):as) = do
  v <- exp c
  case v of
    Value.Bool True  -> exp e
    Value.Bool False -> switch s as

cases :: Source -> Value -> [(Annotated Pat, Annotated Exp)] -> Praxis Value
cases s x [] = throwAt s ("no matching pattern for value " <> quote (pretty (show x)))
cases s x ((p,e):ps) = case alt x p of
  Just c  -> save vEnv $ do
    c
    exp e
  Nothing ->
    cases s x ps

forceBind :: Source -> Value -> Annotated Pat -> Praxis ()
forceBind s v p = case alt v p of Just c  -> c
                                  Nothing -> throwAt s ("no matching pattern for value " <> quote (pretty (show v)))

bind :: Annotated Bind -> Praxis ()
bind ((s, _) :< Bind p x) = do
  x' <- exp x
  forceBind s x' p

alt :: Value -> Annotated Pat -> Maybe (Praxis ())
alt v (_ :< p) = case p of

  PatAt n p
    -> (\c -> do { vEnv %= intro n v; c }) <$> alt v p

  PatCon n p | Value.Con m v <- v
    -> if n /= m then Nothing else case (p, v) of
      (Nothing, Nothing) -> Just (return ())
      (Just p, Just v)   -> alt v p

  PatHole
    -> Just (return ())

  PatLit l -> if match then Just (return ()) else Nothing where
    match = case (l, v) of
      (Bool b,   Value.Bool b') -> b == b'
      (Char c,   Value.Char c') -> c == c'
      (Int i,     Value.Int i') -> i == i'
      _                         -> False

  PatPair p q | Value.Pair p' q' <- v
    -> liftA2 (>>) (alt p' p) (alt q' q)

  PatUnit
    -> Just (return ())

  PatVar n
    -> Just $ vEnv %= intro n v

  _
    -> Nothing
