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
import           Value             (Value)
import qualified Value

import           Control.Monad.Fix (mfix)
import           Data.Array.IO
import           Data.Maybe        (mapMaybe)
import           Prelude           hiding (exp, lookup)

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
  let (ns, es) = unzip $ mapMaybe declVar ds
  mfix (\vs -> do { irrefMapM (\(n, v) -> vEnv %= intro n v) ns vs; irrefMapM (\(_, e) -> exp e) ns es })
  return ()
  where
    declVar = \case
      (_ :< DeclVar n _ e) -> Just (n, e)
      _ -> Nothing

stmt :: Annotated Stmt -> Praxis ()
stmt (_ :< s) = case s of

  StmtBind b -> bind b

  StmtExp e  -> exp e >> return ()


exp :: Annotated Exp -> Praxis Value
exp (_ :< e) = case e of

  Apply f x -> do
    Value.Fun f' <- exp f
    x' <- exp x
    f' x'

  Case e ps -> do
    v <- exp e
    cases v ps

  Cases ps -> do
    l <- use vEnv
    return $ Value.Fun $ \v -> save vEnv $ do { vEnv .= l; cases v ps }

  Con n -> do
    Just da <- daEnv `uses` lookup n
    let DataAltInfo _ at _ = view (annotation . just) da
    return $ case at of
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
    return $ Value.Fun $ \v -> save vEnv $ do { vEnv .= l; forceBind v p; exp e }

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

  Switch alts -> switch alts

  Term.Unit -> return Value.Unit

  Var n -> do
    Just v <- vEnv `uses` lookup n
    return v

  Where x ys -> save vEnv $ do
    decls ys
    exp x


switch :: [(Annotated Exp, Annotated Exp)] -> Praxis Value
switch [] = error "no true switch alternative"
switch ((c,e):as) = do
  v <- exp c
  case v of
    Value.Bool True  -> exp e
    Value.Bool False -> switch as

cases :: Value -> [(Annotated Pat, Annotated Exp)] -> Praxis Value
cases x [] = error ("no matching pattern" ++ show x)
cases x ((p,e):ps) = case alt x p of
  Just c  -> save vEnv $ do
    c
    exp e
  Nothing ->
    cases x ps

forceBind :: Value -> Annotated Pat -> Praxis ()
forceBind v p = case alt v p of Just c  -> c
                                Nothing -> error "no matching pattern" -- TODO

bind :: Annotated Bind -> Praxis ()
bind (_ :< Bind p x) = do
  x' <- exp x
  let Just c = alt x' p
  c

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
