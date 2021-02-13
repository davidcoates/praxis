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
import           Value         (Value)
import qualified Value

import           Data.Array.IO
import           Data.Monoid   (Sum (..))
import           Prelude       hiding (exp, lookup)

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
    Value.Fun f' <- exp f
    x' <- exp x
    f' x'

  Case e ps -> do
    v <- exp e
    cases v ps

  Cases ps -> do
    l <- use vEnv
    let e = Value.Fun $ \v -> save vEnv $ do { vEnv .= l; rec n e; cases v ps }
    return e

  Con n -> do
    Just da <- daEnv `uses` lookup n
    let DataAltInfo _ at _ = view (annotation . just) da
    return $ case at of
      Nothing -> Value.Con n Nothing
      Just _  -> Value.Fun (\v -> return $ Value.Con n (Just v))

  Do ss -> do
    Sum i <- asum (map stmt (init ss))
    let _ :< StmtExp e = last ss
    v <- exp e
    vEnv %= elimN i
    return v

  If a b c -> do
    Value.Bool a' <- exp a
    if a' then exp b else exp c

  Lambda p e -> do
    l <- use vEnv
    let f = Value.Fun $ \v -> save vEnv $ do { vEnv .= l; rec n f; i <- forceBind v p; exp e }
    return f

  Let b x -> do
    i <- bind b
    x' <- exp x
    vEnv %= elimN i
    return x'

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

  Where x bs -> do
    i <- binds bs
    x' <- exp x
    vEnv %= elimN i
    return x'


exp :: Annotated Exp -> Praxis Value
exp = expRec Nothing

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
  Just c  -> do
    i <- c
    e' <- exp e
    vEnv %= elimN i
    return e'
  Nothing ->
    cases x ps

forceBind :: Value -> Annotated Pat -> Praxis Int
forceBind v p = case alt v p of Just i  -> i
                                Nothing -> error "no matching pattern" -- TODO

binds :: [(Annotated Pat, Annotated Exp)] -> Praxis Int
binds bs = sum <$> mapM bind bs

bind :: (Annotated Pat, Annotated Exp) -> Praxis Int
bind (p, x) = do
  x' <- exp x
  let Just i = alt x' p
  i

alt :: Value -> Annotated Pat -> Maybe (Praxis Int)
alt v (_ :< p) = case p of

  PatAt n p
    -> (\c -> do { vEnv %= intro n v; i <- c; return (i+1) }) <$> alt v p

  PatCon n p | Value.Con m v <- v
    -> if n /= m then Nothing else case (p, v) of
      (Nothing, Nothing) -> Just (return 0)
      (Just p, Just v)   -> alt v p

  PatHole
    -> Just (return 0)

  PatLit l -> if match then Just (return 0) else Nothing where
    match = case (l, v) of
      (Bool b,   Value.Bool b') -> b == b'
      (Char c,   Value.Char c') -> c == c'
      (Int i,     Value.Int i') -> i == i'
      _                         -> False

  PatPair p q | Value.Pair p' q' <- v
    -> do
      i <- alt p' p
      j <- alt q' q
      return $ liftA2 (+) i j

  PatUnit
    -> Just (return 0)

  PatVar n
    -> Just $ vEnv %= intro n v >> return 1

  _
    -> Nothing
