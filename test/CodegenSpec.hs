{-# LANGUAGE QuasiQuotes #-}

module CodegenSpec where

import           Test.Hspec
import           Text.RawString.QQ

import qualified Codegen
import           Common
import           Eval              (runMain)
import           Inbuilts          (runWithPrelude)
import           Introspect
import           Praxis
import           Util

import           Control.Exception (finally)
import           Data.IORef
import           GHC.IO.Handle     (hDuplicate, hDuplicateTo)
import           System.Directory  (createDirectoryIfMissing, findExecutable,
                                    getTemporaryDirectory)
import           System.Exit       (ExitCode (..))
import           System.FilePath   ((</>))
import           System.IO
import           System.IO.Unsafe  (unsafePerformIO)
import           System.Process    (readProcessWithExitCode)


-- Code generation: programs are compiled with clang and run, and their output compared with the expected output and
-- with the interpreter's. The tests are skipped when clang is not available.

counter :: IORef Int
counter = unsafePerformIO (newIORef 0)
{-# NOINLINE counter #-}

tempFile :: String -> IO FilePath
tempFile hint = do
  tmp <- getTemporaryDirectory
  let dir = tmp </> "praxis-codegen-test"
  createDirectoryIfMissing True dir
  n <- atomicModifyIORef' counter (\n -> (n + 1, n))
  return (dir </> (hint ++ "." ++ show n))

-- | Compile a program and run it with the given input, returning its output (or the error of the failing stage).
compileAndRun :: String -> String -> IO String
compileAndRun program input = do
  out <- tempFile "prog"
  result <- runWithPrelude $ do
    flags . silent .= True
    program <- lower ProgramT program
    m <- Codegen.run program
    Codegen.compile m out False
  case result of
    Left err -> return err
    Right () -> do
      (code, stdout, stderr) <- readProcessWithExitCode out [] input
      return $ stdout ++ stderr ++ case code of
        ExitSuccess   -> ""
        ExitFailure n -> "exit code " ++ show n ++ "\n"

-- | Run a program with the interpreter, with the given input, returning its output.
interpret :: String -> String -> IO String
interpret program input = do
  inPath <- tempFile "in"
  outPath <- tempFile "out"
  writeFile inPath input
  result <- redirect inPath outPath $ runWithPrelude (eval ProgramT program >> runMain)
  case result of
    Left err -> return err
    Right () -> readFile outPath

-- | Run an action with stdin and stdout redirected to files.
redirect :: FilePath -> FilePath -> IO a -> IO a
redirect inPath outPath action = do
  hFlush stdout
  savedIn <- hDuplicate stdin
  savedOut <- hDuplicate stdout
  inH <- openFile inPath ReadMode
  outH <- openFile outPath WriteMode
  hDuplicateTo inH stdin
  hDuplicateTo outH stdout
  action `finally` do
    hFlush stdout
    hDuplicateTo savedIn stdin
    hDuplicateTo savedOut stdout
    hClose inH
    hClose outH
    hClose savedIn
    hClose savedOut

-- | A program which should produce the expected output, both when compiled and when interpreted.
program :: Maybe FilePath -> String -> String -> String -> String -> Spec
program clang name source input expected = describe name $ do
  it "compiles and runs" $ case clang of
    Nothing -> pendingWith "clang not found"
    Just _  -> compileAndRun source input `shouldReturn` expected
  it "interprets" $ interpret source input `shouldReturn` expected

-- | A program which should produce the expected output when compiled.
compiled :: Maybe FilePath -> String -> String -> String -> String -> Spec
compiled clang name source input expected = describe name $
  it "compiles and runs" $ case clang of
    Nothing -> pendingWith "clang not found"
    Just _  -> compileAndRun source input `shouldReturn` expected


spec :: Spec
spec = do

  clang <- runIO (findExecutable "clang")

  program clang "factorial" [r|
rec
  factorial : I32 -> I32
  factorial = cases
    0 -> 1
    n -> n * factorial (n - 1)

main : () -> ()
main () = put_int (factorial 5)
|] "" "120\n"


  program clang "integers" [r|
sign : I64 -> I64
sign n = switch
  n < 0  -> -1
  n == 0 -> 0
  n > 0  -> 1

main : () -> ()
main () = do
  put_int (sign (-7))
  put_int (sign 0)
  put_int (sign 7)
  put_int (255 + 1 : U8)
  put_int (0 - 1 : U16)
  put_int (0 - 1 : I8)
  put_int (9223372036854775807 : I64)
  put_int (18446744073709551615 : U64)
  print ((3 : U8) < 2, (-1 : I8) < 1, (200 : U8) > 100)
  print (!True, True && False, False || True)
  print (if 1 != 2 then 'y' else 'n')
|] "" "-1\n0\n1\n0\n65535\n-1\n9223372036854775807\n18446744073709551615\n(False, (True, True))\n(False, (False, True))\n'y'\n"


  program clang "let and pairs" [r|
swap : (I32, Char) -> (Char, I32)
swap (x, y) = (y, x)

main : () -> ()
main () = do
  let p = (1, 'a')
  let (c, n) = swap p
  print (c, n)
  let q = ((), (True, 2))
  print q
|] "" "('a', 1)\n((), (True, 2))\n"


  program clang "enums and unboxed data" [r|
enum Color = Red | Green | Blue

datatype Option a = None () | Some a

datatype Shape = Circle I32 | Rect (I32, I32)

next : Color -> Color
next = cases
  Red   -> Green
  Green -> Blue
  Blue  -> Red

unwrap : (Option I32, I32) -> I32
unwrap (o, d) = case o of
  Some x  -> x
  None () -> d

area : Shape -> I32
area = cases
  Circle r    -> 3 * r * r
  Rect (w, h) -> w * h

main : () -> ()
main () = do
  print (next Red, next Blue)
  put_int (unwrap (Some 3, 0))
  put_int (unwrap (None (), 9))
  put_int (area (Circle 2) + area (Rect (3, 4)))
  print (Some Green, Rect (1, 2))
  let n = case Rect (5, 6) of
    Rect (5, y) -> y
    _           -> 0
  put_int n
|] "" "(Green, Red)\n3\n9\n24\n(Some Green, Rect (1, 2))\n6\n"


  program clang "closures" [r|
make_adder : I32 -> I32 -> I32
make_adder n = \x -> x + n

twice : (I32 -> I32, I32) -> I32
twice (f, x) = f (f x)

compose3 : (I32 -> I32, I32 -> I32, I32 -> I32) -> I32 -> I32
compose3 (f, g, h) = \x -> f (g (h x))

apply_all : ((I32 -> I32, I32 -> I32), I32) -> I32
apply_all ((f, g), x) = f x + g x

sub_k : I32 -> I32
sub_k x = x - k where
  k : I32
  k = 1

main : () -> ()
main () = do
  let add3 = make_adder 3
  put_int (twice (add3, 1))
  put_int (twice (compose (add3, make_adder 10), 0))
  let f = compose3 (\x -> x + 1, \x -> x * 2, add3)
  put_int (f 10)
  put_int (f 20)
  let g = if f 0 > 3 then f else add3
  put_int (g 1)
  put_int (apply_all ((add3, f), 1))
  put_int (twice (sub_k, 0))
|] "" "7\n26\n27\n47\n9\n13\n-2\n"


  program clang "closures in data" [r|
datatype Box = Box (I32 -> I32)

datatype Option a = None () | Some a

apply_box : forall &r. (&r Box, I32) -> I32
apply_box (Box f, x) = f x

apply_opt : (Option (I32 -> I32), I32) -> I32
apply_opt (o, x) = case o of
  Some f  -> f x
  None () -> x

main : () -> ()
main () = do
  let b = Box (\x -> x + 1)
  put_int (apply_box (&b, 1) + apply_box (&b, 2))
  let o = Some (\x -> x * 10)
  put_int (apply_opt (o, 1) + apply_opt (o, 2))
  put_int (apply_opt (None (), 5))
  let fs = (\x -> x + 1, \x -> x + 2)
  let (p, q) = fs
  put_int (p 0 + q 0)
  drop b
|] "" "5\n30\n5\n3\n"


  program clang "boxed lists" [r|
rec datatype List a = Nil () | Cons (a, List a)

datatype Option a = None () | Some a

rec
  sum : forall &r. &r List I32 -> I32
  sum = cases
    Nil ()       -> 0
    Cons (x, xs) -> x + sum xs

rec
  map : forall ?v a b. (?v a -> b) -> ?v List a -> List b
  map f = cases
    Nil ()       -> Nil ()
    Cons (x, xs) -> Cons (f x, map f xs)

rec
  consume : List I32 -> ()
  consume = cases
    Nil ()       -> ()
    Cons (_, xs) -> consume xs

rec
  length : forall &r a. &r List a -> I32
  length = cases
    Nil ()       -> 0
    Cons (_, xs) -> 1 + length xs

second : List I32 -> Option I32
second = cases
  Cons (_, Cons (y, _)) -> Some y
  _                     -> None ()

unwrap : (Option I32, I32) -> I32
unwrap (o, d) = case o of
  Some x  -> x
  None () -> d

main : () -> ()
main () = do
  let xs = Cons (1, Cons (2, Cons (3, Nil ())))
  put_int (sum &xs)
  let ys = map (\x -> x * 2) &xs
  put_int (sum &ys)
  put_int (length &ys)
  put_int (unwrap (second ys, 0))
  put_int (unwrap (second (Cons (7, Nil ())), 9))
  consume xs
  let zs = map (\x -> x + 1) (Cons (10, Nil ()))
  print &zs
  let ws = map (\c -> (c, c)) (Cons ('a', Nil ()))
  print &ws
  put_int (read zs in sum zs + length zs)
  drop zs
  drop ws
|] "" "6\n12\n3\n4\n9\nCons (11, Nil ())\nCons (('a', 'a'), Nil ())\n12\n"


  program clang "globals" [r|
rec datatype List a = Nil () | Cons (a, List a)

rec
  sum : forall &r. &r List I32 -> I32
  sum = cases
    Nil ()       -> 0
    Cons (x, xs) -> x + sum xs

inc : I32 -> I32
inc x = x + 1

twice : (I32 -> I32, I32) -> I32
twice (f, x) = f (f x)

xs = Cons (1, Cons (2, Nil ()))
ys = xs
total = sum xs + sum ys
both = (twice (inc, 1), twice (inc, 2))
inc2 = compose (inc, inc)
greeting = "hello"

main : () -> ()
main () = do
  put_int total
  put_int (sum xs + total)
  print both
  put_int (twice (inc2, 0))
  put_int (twice (inc2, 0))
  put_str_ln greeting
  put_str_ln greeting
|] "" "6\n9\n(3, 4)\n4\n4\nhello\nhello\n"


  program clang "arrays" [r|
rec
  fill : (Array I32, USize, I32) -> Array I32
  fill (arr, i, v) = if i == len_array &arr then arr else fill ((arr [ i ] <- v), i + 1, v + 1)

rec
  total : forall &r. (&r Array I32, USize, I32) -> I32
  total (arr, i, acc) = if i == len_array arr then acc else total (arr, i + 1, acc + (arr [ i ]))

main : () -> ()
main () = do
  let arr = new_array (5, \() -> 1)
  print &arr
  put_int (total (&arr, 0, 0))
  let arr = fill (arr, 0, 10)
  put_int (total (&arr, 0, 0))
  print &arr
  drop arr
  let fs = new_array (3, \() -> \x -> x + 1)
  let fs = (fs [ 1 ] <- (\x -> x * 100))
  put_int ((&fs [ 0 ]) 1)
  put_int ((&fs [ 1 ]) 1)
  put_int ((&fs [ 2 ]) 1)
  drop fs
  let empty = new_array (0, \() -> 'x')
  print &empty
  drop empty
|] "" "[1, 1, 1, 1, 1]\n5\n60\n[10, 11, 12, 13, 14]\n2\n100\n2\n[]\n"


  program clang "strings and IO" [r|
main : () -> ()
main () = do
  let s = "héllo" : String
  put_str_ln &s
  print &s
  let t = "tab\there" : String
  print &t
  print ('\n', 'é', 'z')
  put_str "no newline"
  put_str_ln ""
  let n = get_int ()
  put_int (n * 2 : I64)
  let rest = get_str ()
  put_str &rest
  print &rest
  drop s
  drop t
  drop rest
|] "21\nrest of input\n" "héllo\n\"h\\233llo\"\n\"tab\\there\"\n('\\n', ('\\233', 'z'))\nno newline\n42\nrest of input\n\"rest of input\\n\"\n"


  compiled clang "inexhaustive switch" [r|
f : I32 -> I32
f n = switch
  n > 0 -> 1

main : () -> ()
main () = do
  put_int (f 1)
  put_int (f 0)
|] "" "1\nerror: inexhaustive switch\nexit code 1\n"


  compiled clang "missing main" [r|
f : I32 -> I32
f n = n
|] "" "codegen error: missing main function"
