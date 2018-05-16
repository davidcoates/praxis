{-# LANGUAGE TemplateHaskell, RankNTypes #-}

module Compiler
  ( Compiler
  , CompilerState
  , initialState
  , throwError
  , internalError -- Prefer this over Prelude.error
  , Stage(..)

  , get
  , getWith
  , set
  , over

  , run
  , runWith
  , lift
  , liftIO -- ^Lifts an IO computation to the Compiler monad

  -- |Flag lenses
  , debug

  -- |Compiler lenses
  , flags
  , stage
  , imports
  , filename
  , src
  , tokens
  , sugaredAST
  , desugaredAST
  , tEnv
  , vEnv
  , typedAST

  , Env
  , QEnv
  , VEnv
  , freshUniT
  , freshUniP
  , freshUniE
  , freshVar

  , ungeneralise

  , debugPrint
  , debugPutStrLn

  , Value(..) -- TODO
  )
  where

import qualified Parse.Parse.AST as Parse
import qualified Parse.Desugar.AST as Desugar
import qualified Parse.Tokenise.Token as Tokenise
import qualified Check.AST as Check
import Common
import Type
import Source
import Error (Error)

import Inbuilts (inbuilts, TopDecl(..))
import Control.Monad (when)
import Control.Monad.State hiding (get, liftIO)
import Control.Monad.Except hiding (throwError, liftIO)
import qualified Control.Monad.Except (throwError)
import Control.Lens hiding (set, over)
import qualified Control.Lens (set, over)
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Control.Applicative (liftA2)

import Record (Record)
import AST (Lit)


data Stage = Tokenise
           | Parse
           | Desugar
           | Generate
           | Solve
           | Evaluate
-- TODO CodeGenerate

instance Show Stage where
  show Tokenise           = "Tokeniser"
  show Parse              = "Parser"
  show Desugar            = "Desugarer"
  show Generate           = "Inference (Constraint Generator)"
  show Solve              = "Inference (Contraint Solver)"
  show Evaluate           = "Evaluate"

-- |A Context stores all in-scope variables along with their type and how many times they are used.
type Env = [(Name, (Pure, Int))]

-- |Context for top-level declarations
type QEnv = [(Name, QPure)]

type VEnv = [(Name, Value)]

type Token = Tokenise.Annotated Tokenise.Token

data Flags = Flags { _debug :: Bool }
  deriving (Show)

data CompilerState = CompilerState
  { _flags        :: Flags
  , _stage        :: Stage               -- ^Current stage of compilation
  , _freshUnis    :: [String]            -- ^Infinite list of distinct dummy names to use for unification types
  , _freshVars    :: [String]            -- ^Infinite list of distinct dummy names to use for phantom variables
  , _imports      :: [FilePath]          -- ^Loaded modules
  , _filename     :: FilePath            -- ^File path (for error messages)
  , _src          :: String              -- ^Source to compile
  , _tokens       :: [Token]             -- ^List of tokens produced by tokeniser
  , _sugaredAST   :: (Parse.AST)         -- ^AST after parsing of tokens
  , _desugaredAST :: (Desugar.AST)       -- ^AST after desugaring
  , _qtEnv        :: QEnv                -- ^Type environment of top-level functions
  , _tEnv         :: Env                 -- ^Type environment of local functions
  , _kEnv         :: ()                  -- TODO (Kind environment)
  , _typedAST     :: (Check.AST)         -- ^AST after type inference
  , _vEnv         :: VEnv                -- ^Value environment for interpreter
  {-
  , _fname    :: Maybe FilePath            -- ^File path
  , _imports  :: [FilePath]                -- ^Loaded modules
  , _src      :: Maybe L.Text              -- ^File source
  , _ast      :: Maybe Syn.Module          -- ^Frontend AST
  , _tenv     :: Env.Env                   -- ^Typing environment
  , _kenv     :: Map.Map Name Kind         -- ^Kind environment
  , _cenv     :: ClassEnv.ClassEnv         -- ^Typeclass environment
  , _cast     :: Maybe Core.Module         -- ^Core AST
  , _flags    :: Flags.Flags               -- ^Compiler flags
  , _venv     :: CoreEval.ValEnv Core.Expr -- ^Core interpreter environment
  , _denv     :: DataEnv.DataEnv           -- ^Entity dictionary
  , _clenv    :: ClassEnv.ClassHier        -- ^Typeclass hierarchy
  -}

  } deriving (Show)

type Compiler a = ExceptT Error (StateT CompilerState IO) a

defaultFlags :: Flags
defaultFlags = Flags { _debug = True }

get :: Lens' CompilerState a -> Compiler a
get = lift . gets . view

getWith :: Lens' CompilerState a -> (a -> b) -> Compiler b
getWith l f = do
  x <- get l
  return (f x)

set :: Lens' CompilerState a -> a -> Compiler ()
set l x = lift . modify $ Control.Lens.set l x

over :: Lens' CompilerState a -> (a -> a) -> Compiler ()
over l f = do
  x <- get l
  set l (f x)

throwError :: Error -> Compiler a
throwError = Control.Monad.Except.throwError

-- filenameDisplay :: Compiler e String
-- filenameDisplay = fromMaybe "<interactive>" <$> getRaw filename

initialState :: CompilerState
initialState  = CompilerState
  { _flags        = defaultFlags
  , _stage        = unset "stage"
  , _freshUnis    = map ('~':) (fresh ['a'..'z'])
  , _freshVars    = map ('_':) (fresh ['a'..'z'])
  , _imports      = unset "imports" 
  , _filename     = "<stdin>"
  , _src          = unset "src"
  , _tokens       = unset "tokens"
  , _sugaredAST   = unset "sugaredAST"
  , _desugaredAST = unset "desugaredAST"
  , _qtEnv        = map (\(s, t) -> (s, ty t)) inbuilts
  , _tEnv         = unset "tenv"
  , _kEnv         = unset "kenv"
  , _typedAST     = unset "typedAST"
  , _vEnv         = unset "vEnv"
  }
  where unset s = internalError ("unset " ++ s)




-- TODO
data Value = U
           | L Lit
           | R (Record Value)
           | F (Value -> Compiler Value)

instance Show Value where
  show U     = "()"
  show (L l) = show l
  show (R r) = show r
  show (F f) = "<function>"




fresh :: String -> [String]
fresh alpha = concatMap perm [1..]
  where perm :: Int -> [String]
        perm 1 = map (:[]) alpha
        perm n = do { x <- alpha; y <- perm (n-1); return (x:y) }


internalError :: String -> a
internalError s = error ("INTERNAL COMPILER ERROR! " ++ s)


makeLenses ''Flags
makeLenses ''CompilerState



liftIO :: IO a -> Compiler a
liftIO = lift . lift

run :: Compiler a -> IO (Either Error a, CompilerState)
run c = runWith c initialState

runWith :: Compiler a -> CompilerState -> IO (Either Error a, CompilerState)
runWith c s = (runStateT . runExceptT) c s

-- TODO this possibly shouldnt be here
debugPrint :: Show a => a -> Compiler ()
debugPrint = debugPutStrLn . show

debugPutStrLn :: String -> Compiler ()
debugPutStrLn x = do
  b <- get (flags . debug)
  when b $ do
    s <- get stage
    liftIO $ putStrLn ("Output from stage: " ++ show s)
    liftIO $ putStrLn x

-- TODO: Stuff below this probably shouldn't be here...
freshUniT :: Compiler Type
freshUniT = liftA2 (:#) freshUniP freshUniE

freshUniP :: Compiler Pure
freshUniP = do
  (x:xs) <- get freshUnis
  set freshUnis xs
  return (TyUni x)

freshUniE :: Compiler Effects
freshUniE = do
  (x:xs) <- get freshUnis
  set freshUnis xs
  return (singleton (EfUni x))

freshVar :: Compiler Name
freshVar = do
  (x:xs) <- get freshVars
  set freshVars xs
  return x


-- TODO: Allow quantified effects
ungeneralise :: QPure -> Compiler ([Constraint], Pure)
ungeneralise (Forall cs as t) = do
  bs <- sequence (replicate (length as) freshUniP)
  let ft = (`lookup` zip as bs)
  let fe = const Nothing
  let subsP = subsPure ft fe
  return (map (\c -> case c of Class s t -> Class s (subsP t)) cs, subsP t)
