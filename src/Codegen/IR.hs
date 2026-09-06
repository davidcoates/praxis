-- | A small LLVM IR data type and its textual (.ll) printer. Only the subset used by the backend.
module Codegen.IR
  ( Ty(..)
  , Val(..)
  , Operand(..)
  , Instr(..)
  , Terminator(..)
  , Block(..)
  , Function(..)
  , Global(..)
  , Module(..)

  , unit
  , i1
  , i8
  , i32
  , i64
  , closureHeader
  , intConst
  , boolConst
  , unitConst
  , undef
  , null
  , global
  , sizeOf

  , printModule
  , printTy
  ) where

import           Data.Char (isAlphaNum, ord)
import           Data.List (intercalate)
import           Numeric   (showHex)
import           Prelude   hiding (null)


data Ty
  = I Int
  | Ptr
  | Struct [Ty]
  | Arr Int Ty
  | Void
  | Fn Ty [Ty]
  deriving (Eq, Ord)

data Val
  = Local String
  | Global String
  | Int Integer
  | Undef
  | Zero
  | Null
  | StructC [Operand]
  | ArrC [Operand]
  | Str String
  -- ^ A byte string (of the containing array's length), with no implicit terminator.
  deriving (Eq, Ord)

data Operand = Op Ty Val
  deriving (Eq, Ord)

data Instr
  = Arith String Operand Operand
  -- ^ A binary operation (add, sub, mul, sdiv, udiv, and, or, xor, ..)
  | ICmp String Operand Operand
  -- ^ An integer comparison (eq, ne, slt, ult, ..)
  | ExtractValue Operand [Int]
  | InsertValue Operand Operand [Int]
  | Call Ty Operand [Operand]
  -- ^ Return type, callee, arguments
  | Load Ty Operand
  | Store Operand Operand
  -- ^ Value, pointer
  | GEP Ty Operand [Operand]
  -- ^ Base type, pointer, indices
  | Cast String Operand Ty
  -- ^ A conversion (trunc, zext, sext, ptrtoint, inttoptr)
  | Phi Ty [(Operand, String)]
  | Select Operand Operand Operand

data Terminator
  = Ret Operand
  | RetVoid
  | Br String
  | CondBr Operand String String
  | Switch Operand String [(Operand, String)]
  | Unreachable

data Block = Block
  { blockLabel  :: String
  , blockInstrs :: [(Maybe String, Instr)]
  -- ^ Instructions with their result names (Nothing for instructions with no result)
  , blockTerm   :: Terminator
  }

data Function = Function
  { fnName    :: String
  , fnRet     :: Ty
  , fnParams  :: [(Ty, String)]
  , fnBlocks  :: [Block]
  , fnPrivate :: Bool
  }

data Global
  = GlobalVar
    { globalName     :: String
    , globalTy       :: Ty
    , globalInit     :: Val
    , globalConstant :: Bool
    }
  | Declare String Ty [Ty]
  -- ^ An external function: name, return type, parameter types

data Module = Module
  { moduleGlobals   :: [Global]
  , moduleFunctions :: [Function]
  }


-- * Helpers

unit :: Ty
unit = Struct []

i1, i8, i32, i64 :: Ty
i1 = I 1
i8 = I 8
i32 = I 32
i64 = I 64

-- | The header of a closure object: the reference count, the code pointer, and the environment finalizer.
closureHeader :: [Ty]
closureHeader = [i64, Ptr, Ptr]

intConst :: Ty -> Integer -> Operand
intConst ty n = Op ty (Int n)

boolConst :: Bool -> Operand
boolConst b = Op i1 (Int (if b then 1 else 0))

unitConst :: Operand
unitConst = Op unit Zero

undef :: Ty -> Operand
undef ty = Op ty Undef

null :: Operand
null = Op Ptr Null

global :: String -> Operand
global name = Op Ptr (Global name)

-- | A conservative (x86-64) size of a type in bytes, for heap allocation. Aligns every field to 8 bytes, except
-- within arrays, so it is an over-estimate that is always safe.
sizeOf :: Ty -> Int
sizeOf = \case
  I n       -> max 1 ((n + 7) `div` 8)
  Ptr       -> 8
  Struct ts -> sum (map (roundUp . sizeOf) ts)
  Arr n t   -> n * sizeOf t
  Void      -> 0
  Fn _ _    -> 8
  where
    roundUp n = ((n + 7) `div` 8) * 8


-- * Printing

printModule :: Module -> String
printModule (Module globals functions) = unlines $
  map printGlobal globals ++ [""] ++ intercalate [""] (map printFunction functions)

printTy :: Ty -> String
printTy = \case
  I n         -> "i" ++ show n
  Ptr         -> "ptr"
  Struct ts   -> "{ " ++ intercalate ", " (map printTy ts) ++ " }"
  Arr n t     -> "[ " ++ show n ++ " x " ++ printTy t ++ " ]"
  Void        -> "void"
  Fn ret args -> printTy ret ++ " (" ++ intercalate ", " (map printTy args) ++ ")"

printVal :: Val -> String
printVal = \case
  Local name  -> "%" ++ ident name
  Global name -> "@" ++ ident name
  Int n       -> show n
  Undef       -> "undef"
  Zero        -> "zeroinitializer"
  Null        -> "null"
  StructC ops -> "{ " ++ intercalate ", " (map printOperand ops) ++ " }"
  ArrC ops    -> "[ " ++ intercalate ", " (map printOperand ops) ++ " ]"
  Str s       -> "c\"" ++ concatMap escape s ++ "\""
  where
    escape c
      | c == '"' || c == '\\' || ord c < 0x20 || ord c >= 0x7f = '\\' : pad (showHex (ord c `mod` 256) "")
      | otherwise = [c]
    pad s = if length s < 2 then '0' : s else s

-- | Identifiers which are not simple are quoted.
ident :: String -> String
ident name
  | all simple name && not (all (`elem` ['0'..'9']) name) = name
  | otherwise = "\"" ++ concatMap escape name ++ "\""
  where
    simple c = isAlphaNum c || c `elem` ("-$._" :: String)
    escape c
      | c == '"' || c == '\\' || ord c < 0x20 || ord c >= 0x7f = '\\' : pad (showHex (ord c `mod` 256) "")
      | otherwise = [c]
    pad s = if length s < 2 then '0' : s else s

printOperand :: Operand -> String
printOperand (Op ty val) = printTy ty ++ " " ++ printVal val

opVal :: Operand -> String
opVal (Op _ val) = printVal val

printInstr :: (Maybe String, Instr) -> String
printInstr (result, instr) = "  " ++ maybe "" (\name -> "%" ++ ident name ++ " = ") result ++ case instr of
  Arith op a b        -> op ++ " " ++ printOperand a ++ ", " ++ opVal b
  ICmp op a b         -> "icmp " ++ op ++ " " ++ printOperand a ++ ", " ++ opVal b
  ExtractValue a idxs -> "extractvalue " ++ printOperand a ++ concatMap ((", " ++) . show) idxs
  InsertValue a v idxs -> "insertvalue " ++ printOperand a ++ ", " ++ printOperand v ++ concatMap ((", " ++) . show) idxs
  Call ret f args     -> "call " ++ printTy ret ++ " " ++ opVal f ++ "(" ++ intercalate ", " (map printOperand args) ++ ")"
  Load ty p           -> "load " ++ printTy ty ++ ", " ++ printOperand p
  Store v p           -> "store " ++ printOperand v ++ ", " ++ printOperand p
  GEP ty p idxs       -> "getelementptr " ++ printTy ty ++ ", " ++ printOperand p ++ concatMap ((", " ++) . printOperand) idxs
  Cast op a ty        -> op ++ " " ++ printOperand a ++ " to " ++ printTy ty
  Phi ty incoming     -> "phi " ++ printTy ty ++ " " ++ intercalate ", " [ "[ " ++ opVal v ++ ", %" ++ ident l ++ " ]" | (v, l) <- incoming ]
  Select c a b        -> "select " ++ printOperand c ++ ", " ++ printOperand a ++ ", " ++ printOperand b

printTerminator :: Terminator -> String
printTerminator = ("  " ++) . \case
  Ret v               -> "ret " ++ printOperand v
  RetVoid             -> "ret void"
  Br l                -> "br label %" ++ ident l
  CondBr c t f        -> "br " ++ printOperand c ++ ", label %" ++ ident t ++ ", label %" ++ ident f
  Switch v dflt cases -> "switch " ++ printOperand v ++ ", label %" ++ ident dflt ++ " [ " ++ unwords [ printOperand c ++ ", label %" ++ ident l | (c, l) <- cases ] ++ " ]"
  Unreachable         -> "unreachable"

printBlock :: Block -> [String]
printBlock (Block label instrs term) = (ident label ++ ":") : map printInstr instrs ++ [printTerminator term]

printFunction :: Function -> [String]
printFunction (Function name ret params blocks private) =
  [ "define " ++ (if private then "private " else "") ++ printTy ret ++ " @" ++ ident name ++ "(" ++ intercalate ", " [ printTy ty ++ " %" ++ ident p | (ty, p) <- params ] ++ ") {" ]
  ++ concatMap printBlock blocks
  ++ [ "}" ]

printGlobal :: Global -> String
printGlobal = \case
  GlobalVar name ty val constant -> "@" ++ ident name ++ " = private " ++ (if constant then "constant " else "global ") ++ printOperand (Op ty val)
  Declare name ret params -> "declare " ++ printTy ret ++ " @" ++ ident name ++ "(" ++ intercalate ", " (map printTy params) ++ ")"
