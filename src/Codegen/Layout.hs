-- | The runtime representation of Praxis types: the LLVM type of each Praxis type, the generated @copy@, @drop@ and
-- show functions per type, and the layout of closure objects.
module Codegen.Layout
  ( canonType
  , lowerType
  , isRefType
  , intInfo
  , typeName

  , copyValue
  , dropValue
  , showValue

  , makeClosure
  , staticClosure
  , callClosure
  , callClosureBorrowed
  , retain
  , release

  , abort
  , cString
  , stringLiteral
  , constructData
  , dataLayout
  , lookupData
  , lookupCon
  , lookupEnumCon
  , nestValues
  , heapString
  , forLoop
  , loadField
  ) where

import           Check.Type.Instance (Truth (..), isRef, unapplyTypeCon)
import           Codegen.Builder
import           Codegen.IR
import           Common
import           Lower.Monomorphize  (normalizeSubst)
import           Lower.State         (polyDataDecls, specializations)
import           Praxis              hiding (abort, fresh)
import           Print               ()
import           Stage
import           Term                hiding (Op, Switch)

import           Control.Monad       (forM, forM_)
import           Control.Monad.Trans (lift)
import           Data.Bits           (shiftR, (.&.), (.|.))
import           Data.Char           (chr, ord)
import qualified Data.Map.Strict     as Map
import           Prelude             hiding (null)


-- * Types

-- | A canonical form of a type: identity views are stripped, references are made anonymous, and applications of
-- polymorphic data types are resolved to their monomorphic instances. Canonical types are used as cache keys.
canonType :: Type' -> Builder Type'
canonType ty = case view value ty of
  TypeApplyOp op t -> case isRef op of
    Yes -> (\t' -> phantom (TypeApplyOp canonicalRef t')) <$> canonType t
    No  -> canonType t
    _   -> codegenError ("unresolved view in type " ++ typeName ty)
  TypePair a b -> (\a' b' -> phantom (TypePair a' b')) <$> canonType a <*> canonType b
  TypeFn a b   -> (\a' b' -> phantom (TypeFn a' b')) <$> canonType a <*> canonType b
  TypeUnit     -> return ty
  TypeCon _    -> return ty
  TypeApply _ _ -> case unapplyTypeCon ty of
    Just (n, [a]) | n == mkName "Array" -> (\a' -> phantom (TypeApply (phantom (TypeCon n)) a')) <$> canonType a
    Just (n, args) -> do
      polys <- lift $ use (lowerState . polyDataDecls)
      specs <- lift $ use (lowerState . specializations)
      case Map.lookup n polys of
        Just (_ :< DeclTypeData _ _ typePats _) -> do
          let key = map snd (normalizeSubst (zip typePats args))
          case Map.lookup (n, key) specs of
            Just mono -> return (phantom (TypeCon mono))
            Nothing   -> codegenError ("no specialization of data type " ++ typeName ty)
        _ -> codegenError ("unknown type constructor in " ++ typeName ty)
    Nothing -> codegenError ("unexpected type " ++ typeName ty)
  _ -> codegenError ("unexpected type " ++ typeName ty)
  where
    canonicalRef = phantom (TypeRef (mkName "r"))

-- | Whether a type is a reference.
isRefType :: Type' -> Bool
isRefType ty = case view value ty of
  TypeApplyOp op _ -> isRef op == Yes
  _                -> False

-- | The width and signedness of an integral type.
intInfo :: Name -> Maybe (Int, Bool)
intInfo n = case nameString n of
  "I8"    -> Just (8, True)
  "I16"   -> Just (16, True)
  "I32"   -> Just (32, True)
  "I64"   -> Just (64, True)
  "ISize" -> Just (64, True)
  "U8"    -> Just (8, False)
  "U16"   -> Just (16, False)
  "U32"   -> Just (32, False)
  "U64"   -> Just (64, False)
  "USize" -> Just (64, False)
  _       -> Nothing

typeName :: Type' -> String
typeName = unwords . words . fold . pretty

-- | The LLVM type of a Praxis type.
lowerType :: Type' -> Builder Ty
lowerType ty = canonType ty >>= go where
  go t = case view value t of
    TypeApplyOp _ t' -> go t'
    TypeUnit         -> return unit
    TypePair a b     -> Struct <$> mapM go [a, b]
    TypeFn _ _       -> return Ptr
    TypeApply _ _    -> return Ptr -- Array
    TypeCon n        -> conType n
    _                -> codegenError ("unexpected type " ++ typeName t)

  conType n
    | Just (w, _) <- intInfo n = return (I w)
    | otherwise = case nameString n of
        "Bool"   -> return i1
        "Char"   -> return i32
        "Unit"   -> return unit
        "String" -> return Ptr
        _ -> do
          es <- use enums
          ds <- use dataTypes
          case (Map.lookup n es, Map.lookup n ds) of
            (Just _, _) -> return i32
            (_, Just d) -> case dataMode d of
              DataBoxed   -> return Ptr
              DataUnboxed -> dataLayout d
            _ -> codegenError ("unknown type " ++ typeName ty)

-- | The layout of a data type's cell: the tag followed by every constructor's payload.
dataLayout :: DataInfo -> Builder Ty
dataLayout d = do
  payloads <- mapM (lowerType . snd) (dataCons d)
  return (Struct (i32 : payloads))

lookupData :: Name -> Builder DataInfo
lookupData n = use dataTypes >>= \ds -> case Map.lookup n ds of
  Just d  -> return d
  Nothing -> codegenError ("unknown data type " ++ nameString n)

lookupCon :: Name -> Builder (ConInfo, DataInfo, Type')
lookupCon n = use conInfos >>= \cs -> case Map.lookup n cs of
  Just c -> do
    d <- lookupData (conData c)
    return (c, d, snd (dataCons d !! conTag c))
  Nothing -> codegenError ("unknown constructor " ++ nameString n)

lookupEnumCon :: Name -> Builder Int
lookupEnumCon n = use enumCons >>= \cs -> case Map.lookup n cs of
  Just (_, i) -> return i
  Nothing     -> codegenError ("unknown enum constructor " ++ nameString n)

-- | The structure of a (canonical) type, for the structural helpers below.
data Shape
  = Scalar
  | Reference
  | FunctionShape
  | PairOf Type' Type'
  | Data Name DataInfo
  | ArrayOf Type'
  | StringShape

shape :: Type' -> Builder Shape
shape t = case view value t of
  TypeApplyOp _ _ -> return Reference
  TypeUnit        -> return Scalar
  TypePair a b    -> return (PairOf a b)
  TypeFn _ _      -> return FunctionShape
  TypeApply _ a   -> return (ArrayOf a)
  TypeCon n
    | Just _ <- intInfo n -> return Scalar
    | nameString n `elem` ["Bool", "Char", "Unit"] -> return Scalar
    | nameString n == "String" -> return StringShape
    | otherwise -> do
        es <- use enums
        ds <- use dataTypes
        case (Map.lookup n es, Map.lookup n ds) of
          (Just _, _) -> return Scalar
          (_, Just d) -> return (Data n d)
          _           -> codegenError ("unknown type " ++ typeName t)
  _ -> codegenError ("unexpected type " ++ typeName t)

-- | Whether copying and dropping a value of the (canonical) type does nothing.
trivial :: Type' -> Builder Bool
trivial t = shape t >>= \case
  Scalar     -> return True
  Reference  -> return True
  FunctionShape   -> return False
  PairOf a b -> (&&) <$> trivial a <*> trivial b
  Data _ d   -> case dataMode d of
    DataBoxed   -> return False
    DataUnboxed -> and <$> mapM (\(_, p) -> canonType p >>= trivial) (dataCons d)
  ArrayOf _  -> return False
  StringShape        -> return False


-- * Copy and drop

retain, release :: Operand -> Builder ()
retain c = runtimeCall_ "praxis_retain" [c]
release c = runtimeCall_ "praxis_release" [c]

extract :: Ty -> Operand -> Int -> Builder Operand
extract ty v i = instr ty (ExtractValue v [i])

-- | Copy a value of the given type (which must be Copy).
copyValue :: Type' -> Operand -> Builder Operand
copyValue ty v = do
  t <- canonType ty
  triv <- trivial t
  if triv then return v else shape t >>= \case
    FunctionShape -> retain v >> return v
    PairOf a b -> do
      let Op (Struct [ta, tb]) _ = v
      x <- extract ta v 0 >>= copyValue a
      y <- extract tb v 1 >>= copyValue b
      p <- instr (Struct [ta, tb]) (InsertValue (undef (Struct [ta, tb])) x [0])
      instr (Struct [ta, tb]) (InsertValue p y [1])
    Data n d | dataMode d == DataUnboxed -> do
      fn <- copyFunction n d t
      let Op lt _ = v
      instr lt (Call lt (global fn) [v])
    _ -> codegenError ("copy of non-copyable type " ++ typeName t)

copyFunction :: Name -> DataInfo -> Type' -> Builder String
copyFunction n d t = cached copyFns t ("copy " ++ typeName t) $ \name -> do
  lt <- dataLayout d
  defineFunction name lt [lt] $ \[v] -> do
    tag <- extract i32 v 0
    end <- freshLabel "end"
    cases <- forM (zip [0..] (dataCons d)) $ \(i, (_, payload)) -> do
      label <- freshLabel ("con." ++ show i)
      return (i, payload, label)
    terminate (Switch tag end [ (intConst i32 (toInteger i), label) | (i, _, label) <- cases ])
    incoming <- forM cases $ \(i, payload, label) -> do
      newBlock label
      let Struct fields = lt
      p <- extract (fields !! (i + 1)) v (i + 1)
      p' <- copyValue payload p
      v' <- instr lt (InsertValue v p' [i + 1])
      from <- currentBlock
      terminate (Br end)
      return (v', from)
    newBlock end
    r <- instr lt (Phi lt (incoming ++ [(v, "entry")]))
    terminate (Ret r)

-- | Drop a value of the given type (which must be Drop).
dropValue :: Type' -> Operand -> Builder ()
dropValue ty v = do
  t <- canonType ty
  triv <- trivial t
  unless triv $ shape t >>= \case
    FunctionShape -> release v
    PairOf a b -> do
      let Op (Struct [ta, tb]) _ = v
      extract ta v 0 >>= dropValue a
      extract tb v 1 >>= dropValue b
    Data n d -> do
      fn <- dropFunction n d t
      instr_ (Call Void (global fn) [v])
    ArrayOf a -> do
      fn <- dropArrayFunction a t
      instr_ (Call Void (global fn) [v])
    StringShape -> runtimeCall_ "praxis_free" [v]
    _ -> return ()

dropFunction :: Name -> DataInfo -> Type' -> Builder String
dropFunction n d t = cached dropFns t ("drop " ++ typeName t) $ \name -> do
  lt <- dataLayout d
  let Struct fields = lt
  case dataMode d of
    DataUnboxed -> defineFunction name Void [lt] $ \[v] -> do
      tag <- extract i32 v 0
      end <- freshLabel "end"
      cases <- forM (zip [0..] (dataCons d)) $ \(i, (_, payload)) -> (i, payload,) <$> freshLabel ("con." ++ show i)
      terminate (Switch tag end [ (intConst i32 (toInteger i), label) | (i, _, label) <- cases ])
      forM_ cases $ \(i, payload, label) -> do
        newBlock label
        extract (fields !! (i + 1)) v (i + 1) >>= dropValue payload
        terminate (Br end)
      newBlock end
      terminate RetVoid
    DataBoxed -> defineFunction name Void [Ptr] $ \[v] -> do
      tag <- loadField lt v 0
      end <- freshLabel "end"
      cases <- forM (zip [0..] (dataCons d)) $ \(i, (_, payload)) -> (i, payload,) <$> freshLabel ("con." ++ show i)
      terminate (Switch tag end [ (intConst i32 (toInteger i), label) | (i, _, label) <- cases ])
      forM_ cases $ \(i, payload, label) -> do
        newBlock label
        -- The payload is loaded and the cell freed before the payload is dropped, so that dropping a recursive
        -- data type is a tail call.
        p <- loadField lt v (i + 1)
        runtimeCall_ "praxis_free" [v]
        dropValue payload p
        terminate (Br end)
      newBlock end
      terminate RetVoid

dropArrayFunction :: Type' -> Type' -> Builder String
dropArrayFunction elemTy t = cached dropFns t ("drop " ++ typeName t) $ \name -> do
  et <- lowerType elemTy
  triv <- canonType elemTy >>= trivial
  defineFunction name Void [Ptr] $ \[arr] -> do
    unless triv $ do
      len <- instr i64 (Load i64 arr)
      forLoop len $ \i -> do
        p <- instr Ptr (GEP (Struct [i64, Arr 0 et]) arr [intConst i32 0, intConst i32 1, i])
        instr et (Load et p) >>= dropValue elemTy
    runtimeCall_ "praxis_free" [arr]
    terminate RetVoid

-- | A counted loop from 0 to (excluding) the bound.
forLoop :: Operand -> (Operand -> Builder ()) -> Builder ()
forLoop bound body = do
  from <- currentBlock
  header <- freshLabel "loop"
  bodyL <- freshLabel "body"
  end <- freshLabel "end"
  terminate (Br header)
  newBlock header
  -- The phi is completed after the body is generated.
  iName <- fresh
  let i = Op i64 (Local iName)
  next <- instr i64 (Arith "add" i (intConst i64 1))
  done <- instr i1 (ICmp "ult" i bound)
  terminate (CondBr done bodyL end)
  newBlock bodyL
  body i
  bodyEnd <- currentBlock
  terminate (Br header)
  newBlock end
  -- Insert the phi at the start of the header block.
  prependInstr header (Just iName, Phi i64 [(intConst i64 0, from), (next, bodyEnd)])

loadField :: Ty -> Operand -> Int -> Builder Operand
loadField layout p i = do
  let Struct fields = layout
      ty = fields !! i
  fp <- instr Ptr (GEP layout p [intConst i32 0, intConst i32 (toInteger i)])
  instr ty (Load ty fp)


-- * Show

-- | Print a value in the same format as the interpreter's 'show'.
showValue :: Type' -> Operand -> Builder ()
showValue ty v = do
  t <- canonType ty
  shape t >>= \case
    Reference -> let (_ :< TypeApplyOp _ t') = t in showValue t' v
    Scalar -> case view value t of
      TypeUnit -> lit "()"
      TypeCon n
        | Just (w, signed) <- intInfo n -> do
            x <- if w == 64 then return v else instr i64 (Cast (if signed then "sext" else "zext") v i64)
            runtimeCall_ (if signed then "praxis_show_int" else "praxis_show_uint") [x]
        | nameString n == "Bool" -> runtimeCall_ "praxis_show_bool" [v]
        | nameString n == "Char" -> runtimeCall_ "praxis_show_char" [v]
        | nameString n == "Unit" -> lit "()"
        | otherwise -> do
            -- An enum
            fn <- showEnumFunction n t
            instr_ (Call Void (global fn) [v])
      _ -> codegenError ("show: unexpected type " ++ typeName t)
    FunctionShape -> lit "«function»"
    PairOf a b -> do
      let Op (Struct [ta, tb]) _ = v
      lit "("
      extract ta v 0 >>= showValue a
      lit ", "
      extract tb v 1 >>= showValue b
      lit ")"
    Data n d -> do
      fn <- showDataFunction n d t
      instr_ (Call Void (global fn) [v])
    ArrayOf a -> do
      fn <- showArrayFunction a t
      instr_ (Call Void (global fn) [v])
    StringShape -> runtimeCall_ "praxis_show_str" [v]
  where
    lit s = cString s >>= \p -> runtimeCall_ "praxis_show_lit" [p]

showEnumFunction :: Name -> Type' -> Builder String
showEnumFunction n t = cached showFns t ("show " ++ typeName t) $ \name -> do
  es <- use enums
  let Just cons = Map.lookup n es
  defineFunction name Void [i32] $ \[v] -> do
    end <- freshLabel "end"
    cases <- forM (zip [0..] cons) $ \(i, con) -> (i, con,) <$> freshLabel ("con." ++ show i)
    terminate (Switch v end [ (intConst i32 (toInteger i), label) | (i, _, label) <- cases ])
    forM_ cases $ \(_, con, label) -> do
      newBlock label
      cString (nameString con) >>= \p -> runtimeCall_ "praxis_show_lit" [p]
      terminate (Br end)
    newBlock end
    terminate RetVoid

showDataFunction :: Name -> DataInfo -> Type' -> Builder String
showDataFunction n d t = cached showFns t ("show " ++ typeName t) $ \name -> do
  lt <- dataLayout d
  let Struct fields = lt
  argTy <- case dataMode d of
    DataBoxed   -> return Ptr
    DataUnboxed -> return lt
  defineFunction name Void [argTy] $ \[v] -> do
    tag <- case dataMode d of
      DataBoxed   -> loadField lt v 0
      DataUnboxed -> extract i32 v 0
    end <- freshLabel "end"
    cases <- forM (zip [0..] (dataCons d)) $ \(i, con) -> (i, con,) <$> freshLabel ("con." ++ show i)
    terminate (Switch tag end [ (intConst i32 (toInteger i), label) | (i, _, label) <- cases ])
    forM_ cases $ \(i, (con, payload), label) -> do
      newBlock label
      cString (nameString con ++ " ") >>= \p -> runtimeCall_ "praxis_show_lit" [p]
      p <- case dataMode d of
        DataBoxed   -> loadField lt v (i + 1)
        DataUnboxed -> extract (fields !! (i + 1)) v (i + 1)
      showValue payload p
      terminate (Br end)
    newBlock end
    terminate RetVoid

showArrayFunction :: Type' -> Type' -> Builder String
showArrayFunction elemTy t = cached showFns t ("show " ++ typeName t) $ \name -> do
  et <- lowerType elemTy
  defineFunction name Void [Ptr] $ \[arr] -> do
    cString "[" >>= \p -> runtimeCall_ "praxis_show_lit" [p]
    len <- instr i64 (Load i64 arr)
    forLoop len $ \i -> do
      isFirst <- instr i1 (ICmp "eq" i (intConst i64 0))
      sep <- cString ", "
      empty <- cString ""
      p <- instr Ptr (Select isFirst empty sep)
      runtimeCall_ "praxis_show_lit" [p]
      ep <- instr Ptr (GEP (Struct [i64, Arr 0 et]) arr [intConst i32 0, intConst i32 1, i])
      e <- instr et (Load et ep)
      showValue elemTy e
    cString "]" >>= \p -> runtimeCall_ "praxis_show_lit" [p]
    terminate RetVoid


-- * Closures

-- | A closure object holds the reference count, the code pointer, the environment finalizer, and the captures.
closureLayout :: [Ty] -> Ty
closureLayout caps = Struct (closureHeader ++ caps)

-- | The code of a closure over a known function: unpacks (copies of) the captures from the environment and calls
-- the function with the uncurried argument.
thunk :: Known -> [Type'] -> Builder String
thunk k capTys = do
  canon <- mapM canonType capTys
  cached thunks (knownSym k, canon) ("thunk " ++ knownSym k) $ \name -> do
    argTy <- lowerType (knownArg k)
    retTy <- lowerType (knownRet k)
    capLTys <- mapM lowerType capTys
    let layout = closureLayout capLTys
    defineFunction name retTy [Ptr, argTy] $ \[env, x] -> do
      arg <- case capTys of
        [] -> return x
        _  -> do
          caps <- forM (zip [0..] capTys) $ \(i, t) -> loadField layout env (3 + i) >>= copyValue t
          tuple <- nestValues caps
          let Op tupleTy _ = tuple
          p <- instr (Struct [tupleTy, argTy]) (InsertValue (undef (Struct [tupleTy, argTy])) tuple [0])
          instr (Struct [tupleTy, argTy]) (InsertValue p x [1])
      r <- instr retTy (Call retTy (global (knownSym k)) [arg])
      terminate (Ret r)

-- | Values packed in to a right-nested tuple (as captures are).
nestValues :: [Operand] -> Builder Operand
nestValues [] = return unitConst
nestValues [v] = return v
nestValues (v : vs) = do
  rest <- nestValues vs
  let Op tv _ = v
      Op tr _ = rest
      ty = Struct [tv, tr]
  p <- instr ty (InsertValue (undef ty) v [0])
  instr ty (InsertValue p rest [1])

-- | The finalizer for an environment with the given capture types, or null if there is nothing to do.
dropEnv :: [Type'] -> Builder Operand
dropEnv capTys = do
  canon <- mapM canonType capTys
  triv <- and <$> mapM trivial canon
  if triv then return null else do
    name <- cached dropEnvs canon "drop_env" $ \name -> do
      capLTys <- mapM lowerType capTys
      let layout = closureLayout capLTys
      defineFunction name Void [Ptr] $ \[env] -> do
        forM_ (zip [0..] capTys) $ \(i, t) -> loadField layout env (3 + i) >>= dropValue t
        terminate RetVoid
    return (global name)

-- | Allocate a closure over a known function, moving the captured values in to it.
makeClosure :: Known -> [(Type', Operand)] -> Builder Operand
makeClosure k caps = do
  let capTys = map fst caps
  capLTys <- mapM lowerType capTys
  let layout = closureLayout capLTys
  th <- thunk k capTys
  de <- dropEnv capTys
  obj <- runtimeCall "praxis_alloc" Ptr [intConst i64 (toInteger (sizeOf layout))]
  let fields = [intConst i64 1, global th, de] ++ map snd caps
  forM_ (zip [0..] fields) $ \(i, v) -> do
    p <- instr Ptr (GEP layout obj [intConst i32 0, intConst i32 i])
    instr_ (Store v p)
  return obj

-- | A static, immortal closure over a known function with no captures.
staticClosure :: Known -> Builder Operand
staticClosure k = do
  name <- cached statics (knownSym k) ("closure " ++ knownSym k) $ \name -> do
    th <- thunk k []
    addGlobal (GlobalVar name (Struct closureHeader) (StructC [intConst i64 0, global th, null]) False)
  return (global name)

-- | Call a closure, consuming it.
callClosure :: Type' -> Operand -> Operand -> Builder Operand
callClosure retTy c arg = do
  r <- callClosureBorrowed retTy c arg
  release c
  return r

-- | Call a closure without consuming it.
callClosureBorrowed :: Type' -> Operand -> Operand -> Builder Operand
callClosureBorrowed retTy c arg = do
  rt <- lowerType retTy
  code <- loadField (Struct closureHeader) c 1
  instr rt (Call rt code [c, arg])


-- * Constructors

-- | Construct a value of a data type from a constructor's payload.
constructData :: DataInfo -> ConInfo -> Operand -> Builder Operand
constructData d c payload = do
  lt <- dataLayout d
  v <- instr lt (InsertValue (undef lt) (intConst i32 (toInteger (conTag c))) [0])
  v' <- instr lt (InsertValue v payload [conTag c + 1])
  case dataMode d of
    DataUnboxed -> return v'
    DataBoxed -> do
      cell <- runtimeCall "praxis_alloc" Ptr [intConst i64 (toInteger (sizeOf lt))]
      instr_ (Store v' cell)
      return cell


-- * Strings and aborting

-- | A NUL-terminated C string constant.
cString :: String -> Builder Operand
cString s = do
  let bytes = encodeUtf8 s ++ "\0"
      ty = Arr (length bytes) i8
  name <- cached strings ('c' : s) "cstr" $ \name -> addGlobal (GlobalVar name ty (Str bytes) True)
  return (global name)

-- | A static Praxis string: a length followed by the bytes.
stringLiteral :: String -> Builder Operand
stringLiteral s = do
  let bytes = encodeUtf8 s
      ty = Struct [i64, Arr (length bytes) i8]
  name <- cached strings ('s' : s) "str" $ \name ->
    addGlobal (GlobalVar name ty (StructC [intConst i64 (toInteger (length bytes)), Op (Arr (length bytes) i8) (Str bytes)]) True)
  return (global name)

-- | A heap copy of a static string, for an owned string literal.
heapString :: String -> Builder Operand
heapString s = do
  lit <- stringLiteral s
  runtimeCall "praxis_string_copy" Ptr [lit]

-- | Abort the program with a message. Terminates the current block.
abort :: String -> Builder ()
abort msg = do
  p <- cString msg
  runtimeCall_ "praxis_abort" [p]
  terminate Unreachable

encodeUtf8 :: String -> String
encodeUtf8 = concatMap enc where
  enc c
    | n < 0x80    = [c]
    | n < 0x800   = map chr [0xC0 .|. (n `shiftR` 6), 0x80 .|. (n .&. 0x3F)]
    | n < 0x10000 = map chr [0xE0 .|. (n `shiftR` 12), 0x80 .|. ((n `shiftR` 6) .&. 0x3F), 0x80 .|. (n .&. 0x3F)]
    | otherwise   = map chr [0xF0 .|. (n `shiftR` 18), 0x80 .|. ((n `shiftR` 12) .&. 0x3F), 0x80 .|. ((n `shiftR` 6) .&. 0x3F), 0x80 .|. (n .&. 0x3F)]
    where n = ord c
