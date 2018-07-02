{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE TemplateHaskell #-}

module Praxis
  ( Praxis
  , PraxisState
  , Stage(..)
  , emptyState

  , throwError
  , internalError -- Prefer this over Prelude.error

  , get
  , set
  , over

  , save
  , try

  , run
  , runStatic -- TODO Think of a better name for this

  -- |Lift an IO computation to the Praxis monad
  , liftIO

  -- |Flag lenses
  , level

  -- |Praxis lenses
  , filename
  , flags
  , stage
  , tEnv
  , vEnv
  , inClosure

  , freshUniI
  , freshUniP
  , freshUniE
  , freshVar

  , Level(..)
  , log
  , logStr
  )
  where

import           AST                  (Lit)
import qualified Check.AST            as Check
import           Common
import           Env                  (TEnv, VEnv)
import           Error                (Error)
import           Record               (Record)
import           Source
import           Type

import           Control.Applicative  (liftA2)
import           Control.Lens         (Lens', makeLenses, view)
import qualified Control.Lens         (over, set)
import           Control.Monad        (when)
import           Control.Monad.Except (ExceptT, runExceptT)
import qualified Control.Monad.Except (throwError)
import           Control.Monad.State  (StateT, gets, lift, modify, put,
                                       runStateT)
import qualified Control.Monad.State  as State (get)
import           Data.Maybe           (fromMaybe)
import qualified Data.Set             as Set
import           Prelude              hiding (log)
import           System.IO.Unsafe     (unsafePerformIO)

data Stage = Tokenise
           | Parse
           | Desugar
           | Check
           | Generate
           | Solve
           | Evaluate

instance Show Stage where
  show Tokenise = "Tokeniser"
  show Parse    = "Parser"
  show Desugar  = "Desugarer"
  show Check    = "Inference"
  show Generate = "Inference (Constraint Generator)"
  show Solve    = "Inference (Contraint Solver)"
  show Evaluate = "Evaluate"

-- |Logging level
data Level = Normal
           | Debug
           | Trace
  deriving (Show, Eq, Ord)

data Flags = Flags
  { _level  :: Level               -- ^Logging level
  , _static :: Bool                -- ^Set for internal pure computations evaluated at compile time
  } deriving (Show)

data PraxisState = PraxisState
  { _filename  :: String              -- ^File path (for error messages)
  , _flags     :: Flags               -- ^Flags
  , _freshUnis :: [String]            -- ^Infinite list of distinct dummy names to use for unification types
  , _freshVars :: [String]            -- ^Infinite list of distinct dummy names to use for phantom variables
  , _stage     :: Stage               -- ^Current stage of compilation
  , _tEnv      :: TEnv                -- ^Type environment
  , _kEnv      :: ()                  -- TODO (Kind environment)
  , _vEnv      :: VEnv                -- ^Value environment for interpreter
  , _inClosure :: Bool                -- ^Checker (Generator) internal TODO this probably should be put somewhere else
  } deriving (Show)

type Praxis a = ExceptT Error (StateT PraxisState IO) a

defaultFlags :: Flags
defaultFlags = Flags { _level = Normal, _static = False }

get :: Lens' PraxisState a -> Praxis a
get = lift . gets . view

set :: Lens' PraxisState a -> a -> Praxis ()
set l x = lift . modify $ Control.Lens.set l x

over :: Lens' PraxisState a -> (a -> a) -> Praxis ()
over l f = do
  x <- get l
  set l (f x)

throwError :: Error -> Praxis a
throwError = Control.Monad.Except.throwError

emptyState :: PraxisState
emptyState = PraxisState
  { _filename     = "<stdin>"
  , _flags        = defaultFlags
  , _freshUnis    = map ('~':) (fresh ['a'..'z'])
  , _freshVars    = map ('_':) (fresh ['a'..'z'])
  , _stage        = unset "stage"
  , _tEnv         = unset "tenv"
  , _kEnv         = unset "kenv"
  , _vEnv         = unset "vEnv"
  , _inClosure    = unset "inClosure"
  }
  where unset s = internalError ("unset " ++ s)

fresh :: String -> [String]
fresh alpha = concatMap perm [1..]
  where perm :: Int -> [String]
        perm 1 = map (:[]) alpha
        perm n = do { x <- alpha; y <- perm (n-1); return (x:y) }

internalError :: String -> a
internalError s = error ("<<<INTERNAL ERROR>>> " ++ s)

makeLenses ''Flags
makeLenses ''PraxisState

save :: Lens' PraxisState a -> Praxis b -> Praxis b
save l c = do
  x <- get l
  r <- c
  set l x
  return r

-- TODO think of a better name for this
try :: Praxis a -> (Error -> Praxis b) -> (a -> Praxis b) -> Praxis b
try c f g = do
  s <- lift State.get
  (x, s') <- liftIO $ run c s
  case x of
    Left  e -> lift (put s)  >> f e
    Right x -> lift (put s') >> g x

runStatic :: Praxis a -> a
runStatic c = case fst $ unsafePerformIO (run c' emptyState) of
  Left e  -> internalError (show e)
  Right x -> x
  where c' = set (flags . static) True >> c

assert :: Lens' PraxisState a -> (a -> Bool) -> String -> Praxis b -> Praxis b
assert l p s c = do
  x <- get l
  if p x then c else internalError s

liftIO :: IO a -> Praxis a
liftIO io = assert (flags . static) (== False) "liftIO NOT STATIC" (lift (lift io))

run :: Praxis a -> PraxisState -> IO (Either Error a, PraxisState)
run = runStateT . runExceptT

shouldLog :: Level -> Praxis Bool
shouldLog l = do
  l' <- get (flags . level)
  s <- get (flags . static)
  return (l' == Trace || (not s && l' >= l))

log :: Show a => Level -> a -> Praxis ()
log l p = logStr l (show p)

logStr :: Level -> String -> Praxis ()
logStr l x = do
  b <- shouldLog l
  when b $ do
    s <- get stage
    -- We don't use liftIO here so we can show Trace logs
    lift (lift (putStrLn ("Output from stage: " ++ show s)))
    lift (lift (putStrLn x))


-- TODO: Stuff below this probably shouldn't be here...
freshUniI :: Praxis Impure
freshUniI = liftA2 (:#) freshUniP freshUniE

freshUniP :: Praxis Pure
freshUniP = do
  (x:xs) <- get freshUnis
  set freshUnis xs
  return (TyUni x)

freshUniE :: Praxis Effects
freshUniE = do
  (x:xs) <- get freshUnis
  set freshUnis xs
  return (singleton (EfUni x))

freshVar :: Praxis Name
freshVar = do
  (x:xs) <- get freshVars
  set freshVars xs
  return x
