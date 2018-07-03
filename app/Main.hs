module Main where

import           AST
import           Check.AST            (Annotated)
import qualified Env.TEnv             as TEnv (lookup)
import qualified Env.VEnv             as VEnv (lookup)
import           Inbuilts             (initialState)
import           Interpret
import           Praxis
import           Pretty               (indent)
import           Record
import           Type
import           Value

import           Control.Lens.Reified (ReifiedLens (..), ReifiedLens')
import           Control.Monad        (void, when)
import           Data.List            (find, intercalate, stripPrefix)
import           System.Environment
import           System.IO

pretty :: Praxis a -> Praxis b -> Praxis b -> Praxis b
pretty c f g = try c (\e -> liftIO (print e >> putStrLn "^^^ ERRORS OCCURED ^^^") >> f) (const g)

forever :: Praxis a -> Praxis a
forever c = pretty c (forever c) (forever c)

main :: IO ()
main = hSetBuffering stdin LineBuffering >> do
  args <- getArgs
  void $ run (parse args) initialState

parse :: [String] -> Praxis ()
parse xs = do
  xs <- args xs
  parse' xs
    where parse' []  = repl
          parse' [f] = file f
          parse' _   = msg "Too many arguments"

file :: String -> Praxis ()
file f = pretty (interpretFile f :: Praxis (Annotated Program, ())) (return ()) onFileSuccess
  where onFileSuccess = get (flags . interactive) >>= (\i -> if i then repl else runMain)

msg :: String -> Praxis ()
msg s = liftIO (putStrLn s)

runMain :: Praxis ()
runMain = do
  t <- TEnv.lookup "main"
  case t of Nothing -> msg "Missing main function"
            Just (Mono (TyFun (TyRecord r) (TyRecord r' :# _) :# _)) | r == Record.unit && r' == Record.unit ->
              do { Just (F f) <- VEnv.lookup "main"; f (R Record.unit); return () }
            _ -> msg "Ill-typed main function"

repl :: Praxis ()
repl = forever $ do
  s <- liftIO (putStr "> " >> hFlush stdout >> getLine )
  case s of
    ':' : cs -> meta cs
    _        -> eval s

eval :: String -> Praxis ()
eval s = do
  -- TODO fix this so we can have declarations
  (_, v) <- interpret s :: Praxis (Annotated Exp, Value)
  liftIO $ print v

meta :: String -> Praxis ()
meta "?" = msg "help is TODO"
meta s   = msg ("unknown command ':" ++ s ++ "'\nuse :? for help.")


-- Argument handling
data Option = Option [(String, Praxis ())]
            | Flag (Praxis ())

data Arg = Arg { shortName :: String, longName :: String, option :: Option }

myArgs :: [Arg]
myArgs = [ Arg { shortName = "l", longName = "level", option = Option [ ("debug", set (flags . level) Debug)
                                                                      , ("trace", set (flags . level) Trace)
                                                                      ] }
         , Arg { shortName = "i", longName = "interactive", option = Flag (set (flags . interactive) True) }
         ]

args :: [String] -> Praxis [String]
args (x:xs) | Just a <- find (\a -> ("-" ++ shortName a) == x) myArgs
  = case option a of
      Flag p -> p >> args xs
      Option os -> case xs of
        (y:ys) | Just o <- find (\o -> fst o == y) os -> snd o >> args ys
               | otherwise -> err "Unexpected value"
        [] -> err "Missing value"
        where err x = msg (x ++ e) >> return []
              e = " for option '" ++ show (longName a) ++ "' (-" ++ show (shortName a) ++ "). Allowed values are: " ++ intercalate ", " (map fst os)
args (x:xs) = (x:) <$> args xs
args []  = return []
