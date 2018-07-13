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
  , extract

  , save
  , try

  , run
  , runStatic -- TODO Think of a better name for this

  -- |Lift an IO computation to the Praxis monad
  , liftIO

  -- |Flag lenses
  , level
  , interactive

  -- |Praxis lenses
  , filename
  , flags
  , stage
  , tEnv
  , kEnv
  , vEnv
  , system
  , inClosure

  , freshUniI
  , freshUniP
  , freshUniE
  , freshUniK
  , freshVar

  , Level(..)
  , log
  , logStr
  , logList
  )
  where

import           AST                  (Lit)
import qualified Check.AST            as Check
import qualified Check.System         as Check (System)
import           Common
import           Env                  (KEnv, TEnv, VEnv)
import           Error                (Error)
import           Record               (Record)
import           Source
import           Tag                  (Tag (..))
import           Type

import           Control.Applicative  (liftA2)
import           Control.Lens         (Lens', makeLenses, traverseOf, view)
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
  { _level       :: Level             -- ^Logging level
  , _interactive :: Bool
  , _static      :: Bool              -- ^Set for internal pure computations evaluated at compile time
  } deriving (Show)

data Fresh = Fresh
  { _freshUniPs :: [String]
  , _freshUniEs :: [String]
  , _freshUniKs :: [String]
  , _freshVars  :: [String]
  }

instance Show Fresh where
  show _ = "<fresh>"

data PraxisState = PraxisState
  { _filename  :: String              -- ^File path (for error messages)
  , _flags     :: Flags               -- ^Flags
  , _fresh     :: Fresh
  , _stage     :: Stage               -- ^Current stage of compilation
  , _tEnv      :: TEnv                -- ^Type environment
  , _kEnv      :: KEnv                -- ^Kind environment
  , _vEnv      :: VEnv                -- ^Value environment for interpreter
  , _system    :: Check.System        -- ^ TODO rename? put inClosure in here?
  , _inClosure :: Bool                -- ^Checker (Generator) internal TODO this probably should be put somewhere else
  } deriving (Show)

type Praxis a = ExceptT Error (StateT PraxisState IO) a

defaultFlags :: Flags
defaultFlags = Flags { _level = Normal, _interactive = False, _static = False }

get :: Lens' PraxisState a -> Praxis a
get = lift . gets . view

set :: Lens' PraxisState a -> a -> Praxis ()
set l x = lift . modify $ Control.Lens.set l x

over :: Lens' PraxisState a -> (a -> a) -> Praxis ()
over l f = do
  x <- get l
  set l (f x)

extract :: Lens' PraxisState a -> (a -> (b, a)) -> Praxis b
extract l f = do
  x <- get l
  let (c, x') = f x
  set l x'
  return c

throwError :: Error -> Praxis a
throwError = Control.Monad.Except.throwError

defaultFresh = Fresh
  { _freshUniPs   = map (("?a"++) . show) [0..]
  , _freshUniEs   = map (("?e"++) . show) [0..]
  , _freshUniKs   = map (("?k"++) . show) [0..]
  , _freshVars    = map (("?x"++) . show) [0..]
  }

emptyState :: PraxisState
emptyState = PraxisState
  { _filename     = "<stdin>"
  , _flags        = defaultFlags
  , _fresh        = defaultFresh
  , _stage        = unset "stage"
  , _tEnv         = unset "tenv"
  , _kEnv         = unset "kenv"
  , _vEnv         = unset "vEnv"
  , _system       = unset "system"
  , _inClosure    = unset "inClosure"
  }
  where unset s = internalError ("unset " ++ s)

internalError :: String -> a
internalError s = error ("<<<INTERNAL ERROR>>> " ++ s)

makeLenses ''Flags
makeLenses ''Fresh
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

logList :: Show a => Level -> [a] -> Praxis ()
logList l xs = do
  b <- shouldLog l
  when b $ do
    s <- get stage
    lift (lift (putStrLn ("Output from stage: " ++ show s)))
    mapM_ (lift . lift . print) xs

freshUniI :: Praxis (Kinded Impure)
freshUniI = (KindType :<) <$> liftA2 (:#) freshUniP freshUniE

freshUniP :: Praxis (Kinded Type)
freshUniP = do
  (x:xs) <- get (fresh . freshUniPs)
  set (fresh . freshUniPs) xs
  return (KindType :< TyUni x)

freshUniE :: Praxis (Kinded Type)
freshUniE = do
  (x:xs) <- get (fresh . freshUniEs)
  set (fresh . freshUniEs) xs
  return (KindEffect :< TyEffects (Set.singleton (KindEffect :< TyUni x)))

freshUniK :: Praxis Kind
freshUniK = do
  (k:ks) <- get (fresh . freshUniKs)
  set (fresh . freshUniKs) ks
  return (KindUni k)

freshVar :: Praxis Name
freshVar = do
  (x:xs) <- get (fresh . freshVars)
  set (fresh . freshVars) xs
  return x
