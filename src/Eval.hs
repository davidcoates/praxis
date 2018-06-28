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
  , ("getInt", F (\(R _) -> liftIO ((L . Int) <$> readLn)))
  , ("putInt", F (\(L (Int x)) -> liftIO (print x >> pure (R unit))))
  , ("putStrLn", F (\(L (String x)) -> liftIO (putStrLn x >> pure (R unit))))
  ]
  where p :: (Int -> Int -> Int) -> Value
        p f = F (\(R r) -> case unpair r of (L (Int a), L (Int b)) -> pure (L (Int (f a b))))

eval :: Compiler ()
eval = setIn stage Evaluate $ setIn vEnv initialVEnv $ do
  _ :< Program ds <- get typedAST
  mapM_ decl ds
  x <- VEnv.lookup "main"
  case x of
    Just (F f) -> f (R unit) >> pure ()
    _          -> error "missing or illtyped main" -- TODO this shuld be checked earlier!

decl :: Annotated Decl -> Compiler ()
decl (a :< e) = case e of

  DeclFun n t i as ->
    if i == 0 then do
      let [(_, e)] = as 
      e' <- exp e
      intro n e'
    else do
      -- Desugar to lambda and a case
      -- TODO this won't work if the first pattern contains "n" as a var
      (v:vs) <- sequence $ replicate i freshVar 
      let e = F $ \v' -> do { i <- forceBind v' (undefined :< PatVar v); intro n e; v <- exp e'; elim; elimN i; return v }
          e' = fold vs c
          c = undefined :< Case r (map (\(ps, e) -> (undefined :< PatRecord (Record.fromList (map (\p -> (Nothing, p)) ps)), e)) as)
          r  = undefined :< Record (Record.fromList (map (\v -> (Nothing, undefined :< Var v)) (v:vs)))
          fold (v:vs) e = undefined :< Lambda (undefined :< PatVar v) (fold vs e)
          fold     [] e = e
      intro n e

exp :: Annotated Exp -> Compiler Value
exp (a :< e) = case e of

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

  Lambda p e -> return $ F $ \v -> do
    i <- forceBind v p
    e' <- exp e
    elimN i
    return e'
 
  Lit l -> return (L l)

  Record r -> do
    x <- mapM exp r
    return (R x)

  Var n -> do
    Just v <- VEnv.lookup n
    return v

  _ -> error (show (a :< e))

cases :: Value -> [(Annotated Pat, Annotated Exp)] -> Compiler Value
cases x [] = error ("no matching pattern" ++ show x)
cases x ((p,e):ps) = case bind x p of
  Just c  -> do
    i <- c
    e' <- exp e
    elimN i
    return e'
  Nothing ->
    cases x ps

forceBind :: Value -> Annotated Pat -> Compiler Int
forceBind v p = case bind v p of Just i  -> i
                                 Nothing -> error "no matching pattern" -- TODO

-- TODO why is this maybe?
bind :: Value -> Annotated Pat -> Maybe (Compiler Int)
bind x     (_ :< PatVar v)     = Just $ intro v x >> return 1
bind (L l) (_ :< PatLit l')    = if l == l' then Just (return 0) else Nothing
bind (R r) (_ :< PatRecord r') = do
  let vs = map snd $ Record.toCanonicalList r
      ps = map snd $ Record.toCanonicalList r'
  cs <- sequence $ map (\(a, b) -> bind a b) (zip vs ps)
  return (sum <$> sequence cs)
bind _     _ = Nothing
