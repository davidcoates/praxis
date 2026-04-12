module Check.Type.Check
  ( run
  ) where

import           Check.State
import qualified Check.Type.Generate as Generate
import qualified Check.Type.Solve    as Solve
import           Check.Type.State
import           Common
import           Control.Monad.State (runStateT)
import qualified Data.Map.Strict     as Map
import           Introspect
import           Praxis
import           Stage
import           Term


run :: IsTerm a => Annotated KindCheck a -> Praxis (Annotated TypeCheck a)
run term = do
  (term, _) <- runStateT inner emptyTypeLocal
  display TypeCheck "checked term" term `ifFlag` debug
  return term
  where
    inner = do
      term <- Generate.run term >>= Solve.run
      case typeof (view value term) of
        ProgramT -> lift checkMain
        _        -> return ()
      return term

-- | After type-checking a program, validate main's type and record its renamed name.
checkMain :: Praxis ()
checkMain = do
  entry <- (checkState . typeState . varRename) `uses` Map.lookup (mkName "main")
  case entry of
    Nothing     -> return ()
    Just rename -> do
      Just (_, qTy) <- (checkState . typeState . varEnv) `uses` Map.lookup rename
      case view value qTy of
        Mono (_ :< TypeFn (_ :< TypeUnit) (_ :< TypeUnit))
          -> mainName .= Just rename
        _ -> throwAt TypeCheck (view source qTy) $
               "main has bad type " <> pretty qTy <> ", expected () -> ()"
