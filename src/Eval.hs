module Eval
  ( eval
  ) where

import Check.AST
import Compiler
import Env.VEnv (VEnv, intro, elim, elimN)
import qualified Env.VEnv as VEnv (fromList, lookup)
import Inbuilts (inbuilts, TopDecl(..))
import Record
import Tag
import Value

import Data.List (find)
import Prelude hiding (exp)

initialVEnv :: VEnv
initialVEnv = VEnv.fromList
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
eval = setIn stage Evaluate $ setIn vEnv initialVEnv $ do
  _ :< Program ds <- get typedAST
  mapM_ decl ds
  x <- VEnv.lookup "main"
  case x of
    Just (F f) -> f U >> pure ()
    _          -> error "missing or illtyped main" -- TODO this shuld be checked earlier!

decl :: Annotated Decl -> Compiler ()
decl (_ :< DeclFun n t i as) = undefined -- TODO FIXME
{-
do
  e' <- exp e
  l <- get vEnv
  set vEnv ((n, e'):l)
-}


exp :: Annotated Exp -> Compiler Value
exp (t :< e) = case e of

  Apply f x -> do
    F f' <- exp f
    x' <- exp x
    f' x'

  Case e ps -> do
    e' <- exp e
    cases e' ps

  If a b c -> do
    L (Bool a') <- exp a
    if a' then exp b else exp c

  Lambda (_ :< PatVar n) e -> return $ F $ \v -> do -- TODO FIXME
    intro n v
    e' <- exp e
    elim
    return e'
 
  Lit l -> return (L l)

  Record r -> do
    x <- mapM exp r
    return (R x)

  Var n -> do
    Just v <- VEnv.lookup n
    return v

  _ -> error (show (t :< e))

cases :: Value -> [(Annotated Pat, Annotated Exp)] -> Compiler Value
cases x [] = error "no matching pattern"
cases x ((p,e):ps) = case bind x p of
  Just c  -> do
    i <- c
    e' <- exp e
    elimN i
    return e'
  Nothing ->
    cases x ps

-- TODO
bind :: Value -> Annotated Pat -> Maybe (Compiler Int)
bind x     (_ :< PatVar v)            = Just $ intro v x >> return 1
bind (L l) (_ :< PatLit l') | l == l' = Just $ return 0
bind _     (_ :< PatRecord _)         = Just $ return 0 -- TODO FIXME
bind _     _ = Nothing
