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
    let (names, exps) = unzip [ (name, exp) | (_ :< DeclTerm name _ exp) <- decls ]
    -- To support mutual recursion, each function needs to see the evaluation of all other functions (including itself).
    -- Leverage mfix to find the fixpoint.
    mfix $ \values -> do
      -- Evaluate each of the functions in turn, with all of the evaluations in the environment
      -- Note: The use of irrefMapM here is essential to avoid divergence of mfix.
      irrefMapM (\(name, value) -> vEnv %= Env.intro name value) names values
      mapM evalExp exps
    return ()

  DeclTerm name _ exp -> do
    value <- evalExp exp
    vEnv %= Env.intro name value

  _ -> return ()


evalStmt :: Annotated Stmt -> Praxis (Maybe Value)
evalStmt (_ :< stmt) = case stmt of

  StmtBind bind -> evalBind bind >> return Nothing

  StmtExp exp   -> Just <$> evalExp exp


evalExp :: Annotated Exp -> Praxis Value
evalExp ((src, _) :< exp) = case exp of

  Apply f x -> do
    Value.Fun f <- evalExp f
    x <- evalExp x
    f x

  Case exp alts -> do
    val <- evalExp exp
    evalCases src val alts

  Cases alts -> do
    l <- use vEnv
    return $ Value.Fun $ \val -> save vEnv $ do { vEnv .= l; evalCases src val alts }

  Con name -> do
    Just dataAlt <- daEnv `uses` Env.lookup name
    let DataConInfo { argType } = view (annotation . just) dataAlt
    return $ case argType of
      Nothing -> Value.Con name Nothing
      Just _  -> Value.Fun (\val -> return $ Value.Con name (Just val))

  Defer exp1 exp2 -> do
    val <- evalExp exp1
    evalExp exp2
    return val

  If condExp thenExp elseExp -> do
    Value.Bool cond <- evalExp condExp
    if cond then evalExp thenExp else evalExp elseExp

  Lambda pat exp -> do
    l <- use vEnv
    return $ Value.Fun $ \val -> save vEnv $ do { vEnv .= l; forceBind src val pat; evalExp exp }

  Let bind exp -> save vEnv $ do
    evalBind bind
    evalExp exp

  Lit lit -> case lit of
    Bool val   -> pure $ Value.Bool val
    Char val   -> pure $ Value.Char val
    Int val    -> pure $ Value.Int  val
    String val -> Value.Array <$> Value.fromString val

  Read _ exp -> evalExp exp

  Pair exp1 exp2 -> Value.Pair <$> evalExp exp1 <*> evalExp exp2

  Seq exp1 exp2 -> do
    evalExp exp1
    val <- evalExp exp2
    return val

  Sig exp _ -> evalExp exp

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

evalCases :: Source -> Value -> [(Annotated Pat, Annotated Exp)] -> Praxis Value
evalCases src val [] = throwAt src ("no matching pattern for value " <> quote (pretty (show val)))
evalCases src val ((pat,exp):alts) = case tryBind val pat of
  Just doBind -> save vEnv $ do
    doBind
    evalExp exp
  Nothing ->
    evalCases src val alts

forceBind :: Source -> Value -> Annotated Pat -> Praxis ()
forceBind src val pat = case tryBind val pat of
  Just doBind -> doBind
  Nothing -> throwAt src ("no matching pattern for value " <> quote (pretty (show val)))

evalBind :: Annotated Bind -> Praxis ()
evalBind ((src, _) :< Bind pat exp) = do
  exp <- evalExp exp
  forceBind src exp pat

tryBind :: Value -> Annotated Pat -> Maybe (Praxis ())
tryBind val (_ :< pat) = case pat of

  PatAt name pat
    -> (\doBind -> do { vEnv %= Env.intro name val; doBind }) <$> tryBind val pat

  PatCon patCon pat | Value.Con valCon val <- val
    -> if patCon /= valCon then Nothing else case (pat, val) of
      (Nothing, Nothing)   -> Just (return ())
      (Just pat, Just val) -> tryBind val pat

  PatHole
    -> Just (return ())

  PatLit pat -> if match then Just (return ()) else Nothing where
    match = case (pat, val) of
      (Bool v, Value.Bool v') -> v == v'
      (Char v, Value.Char v') -> v == v'
      (Int v,  Value.Int  v') -> v == v'
      _                       -> False

  PatPair pat1 pat2 | Value.Pair val1 val2 <- val
    -> liftA2 (>>) (tryBind val1 pat1) (tryBind val2 pat2)

  PatUnit
    -> Just (return ())

  PatVar name
    -> Just $ vEnv %= Env.intro name val
  _
    -> Nothing
