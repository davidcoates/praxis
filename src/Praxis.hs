{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE TemplateHaskell #-}

module Praxis
  ( Praxis
  , PraxisState
  , Stage(..)
  , emptyState

  , throwError
  , internalError -- Prefer this over Prelude.error

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

  , freshUniT
  , freshUniK
  , freshVar
  , reuse

  , Level(..)
  , log
  , logStr
  , logList

 {-
  , require
  , requireAll
 -}
  )
  where

import           AST                  (Lit)
import qualified Check.System         as Check (System)
import           Check.Type.Annotate  (Typed)
import           Common
import           Env                  (KEnv, TEnv, VEnv)
import           Error                (Error)
import           Record               (Record)
import           Stage
import           Type

import           Control.Applicative  (liftA2)
import           Control.Lens         (Lens', makeLenses, traverseOf)
import           Control.Monad        (when)
import           Control.Monad.Except (ExceptT, runExceptT)
import qualified Control.Monad.Except (throwError)
import           Control.Monad.State  (StateT, gets, lift, runStateT)
import qualified Control.Monad.State  as State (get, modify, put)
import           Data.Maybe           (fromMaybe)
import qualified Data.Set             as Set
import           Prelude              hiding (log)
import           System.IO.Unsafe     (unsafePerformIO)

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
  { _freshUniTs :: [String]
  , _freshUniEs :: [String]
  , _freshUniKs :: [String]
  , _freshVars  :: [String]
  }

instance Show Fresh where
  show _ = "<fresh>"

data PraxisState = PraxisState
  { _filename :: String              -- ^File path (for error messages)
  , _flags    :: Flags               -- ^Flags
  , _fresh    :: Fresh
  , _stage    :: Stage               -- ^Current stage of compilation
  , _tEnv     :: TEnv                -- ^Type environment
  , _kEnv     :: KEnv                -- ^Kind environment
  , _vEnv     :: VEnv                -- ^Value environment for interpreter
  , _system   :: Check.System        -- ^ TODO rename?
  }

instance Show PraxisState where
  show s = "<praxis state>"

type Praxis = ExceptT Error (StateT PraxisState IO)

defaultFlags :: Flags
defaultFlags = Flags { _level = Normal, _interactive = False, _static = False }


throwError :: Error -> Praxis a
throwError = Control.Monad.Except.throwError

defaultFresh = Fresh
  { _freshUniTs   = map (("?t"++) . show) [0..]
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
  }
  where unset s = internalError ("unset " ++ s)

internalError :: String -> a
internalError s = error ("<<<INTERNAL ERROR>>> " ++ s)

makeLenses ''Flags
makeLenses ''Fresh
makeLenses ''PraxisState

save :: Lens' PraxisState a -> Praxis b -> Praxis b
save l c = do
  x <- use l
  r <- c
  l .= x
  return r

-- TODO think of a better name for this
try :: Praxis a -> (Error -> Praxis b) -> (a -> Praxis b) -> Praxis b
try c f g = do
  s <- lift State.get
  (x, s') <- liftIO $ run c s
  case x of
    Left  e -> lift (State.put s)  >> f e
    Right x -> lift (State.put s') >> g x

runStatic :: PraxisState -> Praxis a -> a
runStatic s c = case fst $ unsafePerformIO (run c' s) of
  Left e  -> internalError (show e)
  Right x -> x
  where c' = (flags . static .= True) >> c

assert :: Lens' PraxisState a -> (a -> Bool) -> String -> Praxis b -> Praxis b
assert l p s c = do
  x <- use l
  if p x then c else internalError s

liftIO :: IO a -> Praxis a
liftIO io = assert (flags . static) (== False) "liftIO NOT STATIC" (lift (lift io))

run :: Praxis a -> PraxisState -> IO (Either Error a, PraxisState)
run = runStateT . runExceptT

shouldLog :: Level -> Praxis Bool
shouldLog l = do
  l' <- use (flags . level)
  s <- use (flags . static)
  return (l' == Trace || (not s && l' >= l))

log :: Show a => Level -> a -> Praxis ()
log l p = logStr l (show p)

logStr :: Level -> String -> Praxis ()
logStr l x = do
  b <- shouldLog l
  when b $ do
    s <- use stage
    -- We don't use liftIO here so we can show static Trace logs
    lift (lift (putStrLn ("Output from stage: " ++ show s)))
    lift (lift (putStrLn x))

logList :: Show a => Level -> [a] -> Praxis ()
logList l xs = do
  b <- shouldLog l
  when b $ do
    s <- use stage
    lift (lift (putStrLn ("Output from stage: " ++ show s)))
    mapM_ (lift . lift . print) xs

freshUniT :: Praxis (Typed Type)
freshUniT = do
  (x:xs) <- use (fresh . freshUniTs)
  fresh . freshUniTs .= xs
  return ((Phantom, ()) :< TyUni x)

freshUniK :: Praxis Kind
freshUniK = do
  (k:ks) <- use (fresh . freshUniKs)
  fresh . freshUniKs .= ks
  return (KindUni k)

freshVar :: Praxis Name
freshVar = do
  (x:xs) <- use (fresh . freshVars)
  fresh . freshVars .= xs
  return x

-- This will fuck things up if the name is still used somewhere
reuse :: Name -> Praxis ()
reuse _ = pure ()
{-
reuse n@('?':c:_) = over (fresh . f c) (n:)
  where f 'a' = freshUniTs
        f 'e' = freshUniEs
        f 'k' = freshUniKs
-}

