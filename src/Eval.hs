{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}

module Eval
  ( runExp
  , runProgram
  ) where

import           Common
import qualified Env.Env           as Env
import           Praxis
import           Stage
import           Term
import qualified Value
import           Value             (Value)

import           Control.Monad.Fix (mfix)
import           Data.Array.IO
import           Data.List         (partition)
import           Data.Maybe        (mapMaybe)

runExp :: Annotated Exp -> Praxis Value
runExp exp = save stage $ do
  stage .= Evaluate
  clearTerm `ifFlag` debug
  evalExp exp

runProgram :: Annotated Program -> Praxis ()
runProgram program = save stage $ do
  stage .= Evaluate
  clearTerm `ifFlag` debug
  evalProgram program

evalProgram :: Annotated Program -> Praxis ()
evalProgram (_ :< Program decls) = do
  traverse evalDecl decls
  return ()

-- | A helper for decls, irrefutably matching the [b] argument
irrefMapM :: Monad m => ((a, b) -> m c) -> [a] -> [b] -> m [c]
irrefMapM f as bs = case as of
  []     -> return []
  (a:as) -> case bs of
    ~(b:bs) -> do
      c <- f (a, b)
      cs <- irrefMapM f as bs
      return (c : cs)

evalDecl :: Annotated Decl -> Praxis ()
evalDecl (_ :< decl) = case decl of

  DeclRec decls -> do
    let (names, exps) = unzip [ (name, exp) | (_ :< DeclVar name _ exp) <- decls ]
    -- To support mutual recursion, each function needs to see the evaluation of all other functions (including itself).
    -- Leverage mfix to find the fixpoint.
    mfix $ \values -> do
      -- Evaluate each of the functions in turn, with all of the evaluations in the environment
      -- Note: The use of irrefMapM here is essential to avoid divergence of mfix.
      irrefMapM (\(name, value) -> vEnv %= Env.intro name value) names values
      mapM evalExp exps
    return ()

  DeclVar name _ exp -> do
    value <- evalExp exp
    vEnv %= Env.intro name value

  _ -> return ()


evalExp :: Annotated Exp -> Praxis Value
evalExp ((src, Just t) :< exp) = case exp of

  Apply f x -> do
    Value.Fun f <- evalExp f
    x <- evalExp x
    f x

  Case exp alts -> do
    val <- evalExp exp
    evalCase src val alts

  Cases alts -> do
    l <- use vEnv
    return $ Value.Fun $ \val -> save vEnv $ do { vEnv .= l; evalCase src val alts }

  Con name -> do
    case t of
      (_ :< TyFun _ _) -> return $ Value.Fun (\val -> return $ Value.Data name val)
      _                -> return $ Value.Enum name

  Defer exp1 exp2 -> do
    val <- evalExp exp1
    evalExp exp2
    return val

  If condExp thenExp elseExp -> do
    Value.Bool cond <- evalExp condExp
    if cond then evalExp thenExp else evalExp elseExp

  Lambda pat exp -> do
    l <- use vEnv
    return $ Value.Fun $ \val -> save vEnv $ do { vEnv .= l; forceMatch src val pat; evalExp exp }

  Let bind exp -> save vEnv $ do
    evalBind bind
    evalExp exp

  Lit lit -> pure $ case lit of
    Bool val   -> Value.Bool val
    Char val   -> Value.Char val
    Int val    -> Value.Int val
    String val -> Value.String val

  Read _ exp -> evalExp exp

  Pair exp1 exp2 -> Value.Pair <$> evalExp exp1 <*> evalExp exp2

  Seq exp1 exp2 -> do
    evalExp exp1
    val <- evalExp exp2
    return val

  Sig exp _ -> evalExp exp

  Specialise exp _ -> evalExp exp

  Switch alts -> evalSwitch src alts

  Term.Unit -> return Value.Unit

  Var var -> do
    entry <- vEnv `uses` Env.lookup var
    case entry of
       Just val -> return val
       Nothing  -> throwAt src ("unknown variable " <> quote (pretty var))

  Where exp decls -> save vEnv $ do
    traverse evalDecl decls
    evalExp exp


evalSwitch :: Source -> [(Annotated Exp, Annotated Exp)] -> Praxis Value
evalSwitch src [] = throwAt src ("inexhaustive switch" :: String)
evalSwitch src ((condExp,bodyExp):alts) = do
  cond <- evalExp condExp
  case cond of
    Value.Bool True  -> evalExp bodyExp
    Value.Bool False -> evalSwitch src alts

evalCase :: Source -> Value -> [(Annotated Pat, Annotated Exp)] -> Praxis Value
evalCase src val [] = throwAt src ("no matching pattern for value " <> quote (pretty (show val)))
evalCase src val ((pat,exp):alts) = case tryMatch val pat of
  Just doMatch -> save vEnv $ do
    doMatch
    evalExp exp
  Nothing ->
    evalCase src val alts

forceMatch :: Source -> Value -> Annotated Pat -> Praxis ()
forceMatch src val pat = case tryMatch val pat of
  Just doMatch -> doMatch
  Nothing -> throwAt src ("no matching pattern for value " <> quote (pretty (show val)))

evalBind :: Annotated Bind -> Praxis ()
evalBind ((src, _) :< Bind pat exp) = do
  exp <- evalExp exp
  forceMatch src exp pat

tryMatch :: Value -> Annotated Pat -> Maybe (Praxis ())
tryMatch val (_ :< pat) = case pat of

  PatAt name pat
    -> (\doMatch -> do { vEnv %= Env.intro name val; doMatch }) <$> tryMatch val pat

  PatData name pat | Value.Data name' val <- val
    -> if name == name' then tryMatch val pat else Nothing

  PatEnum name | Value.Enum name' <- val
    -> if name == name' then Just (return ()) else Nothing

  PatHole
    -> Just (return ())

  PatLit pat -> if match then Just (return ()) else Nothing where
    match = case (pat, val) of
      (Bool v, Value.Bool v') -> v == v'
      (Char v, Value.Char v') -> v == v'
      (Int v,  Value.Int  v') -> v == v'
      _                       -> False

  PatPair pat1 pat2 | Value.Pair val1 val2 <- val
    -> liftA2 (>>) (tryMatch val1 pat1) (tryMatch val2 pat2)

  PatUnit
    -> Just (return ())

  PatVar name
    -> Just $ vEnv %= Env.intro name val
  _
    -> Nothing
