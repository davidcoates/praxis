module Inbuilts
  ( initialState
  ) where

import           Control.Lens (set)

import           AST          (Lit (..))
import           Compiler     (CompilerState, emptyState, liftIO, runStatic,
                               tEnv, vEnv)
import           Env.TEnv     (TEnv)
import qualified Env.TEnv     as TEnv (fromList)
import           Env.VEnv     (VEnv)
import qualified Env.VEnv     as VEnv (fromList)
import           Error
import           Parse        (parseFree)
import           Record
import           Source       (Source)
import           Tag
import           Type
import           Value

initialState :: CompilerState
initialState = set tEnv initialTEnv $ set vEnv initialVEnv $ emptyState

-- TODO
mono :: String -> Type
mono s = let (_ :< t) = runStatic (parseFree s) :: Tag Source Impure in Mono t

poly :: String -> Type
poly s = let (_ :< t :# _) = runStatic (parseFree s) :: Tag Source Impure in Forall [] (g t) t
  where g (TyPrim _)         = []
        g (TyRecord r)       = concatMap g r
        g (TyUni _)          = []
        g (TyFun a (b :# _)) = g a ++ g b
        g (TyVar s)          = [s]
        g (TyBang p)         = g p

prelude :: [(Name, Type, Value)]
prelude =
  [ ("add",      mono "(Int, Int) -> Int",     lift (+))
  , ("sub",      mono "(Int, Int) -> Int",     lift (-))
  , ("mul",      mono "(Int, Int) -> Int",     lift (*))
  , ("getInt",   mono "() -> Int # StdIn",     F (\(R _) -> liftIO ((L . Int) <$> readLn)))
  , ("putInt",   mono "Int -> () # StdOut",    F (\(L (Int x)) -> liftIO (print x >> pure (R unit))))
  , ("putStrLn", mono "String -> () # StdOut", F (\(L (String x)) -> liftIO (putStrLn x >> pure (R unit))))
  , ("dot",      poly "(b -> c, a -> b) -> (a -> c)", F (\(R r) -> case unpair r of (F f, F g) -> pure (F (\x -> g x >>= f))))
  ]
  where lift :: (Int -> Int -> Int) -> Value
        lift f = F (\(R r) -> case unpair r of (L (Int a), L (Int b)) -> pure (L (Int (f a b))))


initialVEnv :: VEnv
initialVEnv = VEnv.fromList (map (\(n, _, v) -> (n, v)) prelude)

initialTEnv :: TEnv
initialTEnv = TEnv.fromList (map (\(n, t, _) -> (n, t)) prelude)

