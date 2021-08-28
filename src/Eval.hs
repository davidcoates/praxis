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

stmt :: Annotated Stmt -> Praxis ()
stmt (_ :< s) = case s of

  StmtDecl d -> decl d

  StmtExp e  -> exp e >> return ()


rec :: Maybe Name -> Value -> Praxis ()
rec n v = case n of
  Just n  -> vEnv %= intro n v
  Nothing -> return ()

expRec :: Maybe Name -> Annotated Exp -> Praxis Value
expRec n (_ :< e) = case e of -- TODO should expRec be in more cases below?

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
    let f = Value.Fun $ \v -> save vEnv $ do { vEnv .= l; rec n f; forceBind v p; exp e }
    return f

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
    mapM_ decl ys
    exp x


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
  Just c  -> save vEnv $ do
    c
    exp e
  Nothing ->
    cases x ps

forceBind :: Value -> Annotated Pat -> Praxis ()
forceBind v p = case alt v p of Just c  -> c
                                Nothing -> error "no matching pattern" -- TODO

bind :: (Annotated Pat, Annotated Exp) -> Praxis ()
bind (p, x) = do
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
    -> do
      alt p' p
      alt q' q
      Just $ return ()

  PatUnit
    -> Just (return ())

  PatVar n
    -> Just $ vEnv %= intro n v

  _
    -> Nothing
