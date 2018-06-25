module Eval
  ( eval
  ) where

import Compiler
import Check.AST
import Tag
import Data.List (find)
import Record

initialEnv :: VEnv
initialEnv = 
  [ ("add", p (+))
  , ("sub", p (-))
  , ("mul", p (*))
  , ("getInt", F (\U -> liftIO ((L . Int) <$> readLn)))
  , ("putInt", F (\(L (Int x)) -> liftIO (print x >> pure U)))
  , ("putStrLn", F (\(L (String x)) -> liftIO (putStrLn x >> pure U)))
  ]
  where p :: (Int -> Int -> Int) -> Value
        p f = F (\(R r) -> case unpair r of (L (Int a), L (Int b)) -> pure (L (Int (f a b))))

eval :: Compiler ()
eval = do
  set stage Evaluate
  set vEnv initialEnv
  _ :< Program ds <- get typedAST
  mapM_ evalDecl ds
  l <- get vEnv
  case  lookup "main" l of
    Just (F f) -> f U >> pure ()
    _          -> error "missing or illtyped main" -- TODO this shuld be checked earlier!

evalDecl :: Annotated Decl -> Compiler ()
evalDecl (_ :< DeclFun n t i as) = undefined -- TODO FIXME
{-
do
  e' <- evalExp e
  l <- get vEnv
  set vEnv ((n, e'):l)
-}


evalExp :: Annotated Exp -> Compiler Value
evalExp (t :< e) = case e of

  Apply f x -> do
    F f' <- evalExp f
    x' <- evalExp x
    f' x'

  Case e ps -> do
    e' <- evalExp e
    cases e' ps

  If a b c -> do
    L (Bool a') <- evalExp a
    if a' then evalExp b else evalExp c

  Lambda (_ :< PatVar n) e -> return $ F $ \v -> do -- TODO FIXME
    over vEnv ((n,v):)
    e' <- evalExp e
    over vEnv tail
    return e'
 
  Lit l -> return (L l)

  Record r -> do
    x <- mapM evalExp r
    return (R x)

  Var n -> do
    Just v <- getWith vEnv (lookup n)
    return v

  _ -> error (show (t :< e))

cases :: Value -> [(Annotated Pat, Annotated Exp)] -> Compiler Value
cases x [] = error "no matching pattern"
cases x ((p,e):ps) = case bind x p of
  Just c  -> do
    i <- c
    e' <- evalExp e
    over vEnv (drop i)
    return e'
  Nothing ->
    cases x ps

-- TODO
bind :: Value -> Annotated Pat -> Maybe (Compiler Int)
bind x     (_ :< PatVar v)            = Just $ over vEnv ((v, x):) >> return 1
bind (L l) (_ :< PatLit l') | l == l' = Just $ return 0
bind _     (_ :< PatRecord _)         = Just $ return 0 -- TODO FIXME
bind _     _ = Nothing
