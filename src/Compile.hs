module Compile
  ( compileFile
  ) where

import           Check           (check)
import           Common
import           Compile.CodeGen
import           Env
import           Parse           (parse)
import           Praxis
import           Prelude         hiding (lookup)
import           Term

compileFile :: Praxis ()
compileFile = do
  inF <- use infile
  outF <- use outfile
  case (inF, outF) of
     (Just inF, Just outF) -> do
       inS <- liftIO (readFile inF)
       outS <- compile inS
       liftIO (writeFile outF outS)
       return ()
     _                     -> throw "missing infile and/or outfile"

compile :: String -> Praxis String
compile input = do
  x <- parse input :: Praxis (Annotated Program)
  y <- check x
  t <- tEnv `uses` lookup "main"
  case t of
    Nothing -> throw "missing main function"
    Just (_ :< Forall [] (_ :< TyFun (_ :< TyUnit) (_ :< TyUnit))) -> return ()
    Just t -> throwAt (view source t) $ pretty "main function has bad type " <> quote (pretty t) <> pretty ", expected () -> ()"
  codeGen y
