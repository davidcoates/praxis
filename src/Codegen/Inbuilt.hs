-- | Implementations of the inbuilt functions, generated on demand as functions at each (monomorphic) type they are used
-- at. An applied inbuilt is a direct call to the generated function; an inbuilt used as a value is a static closure
-- over it.
module Codegen.Inbuilt
  ( inbuiltKnown
  ) where

import           Codegen.Builder
import           Codegen.IR
import           Codegen.Layout
import           Common
import           Term            hiding (Op)

import           Prelude         hiding (null)


-- | The known function implementing an inbuilt at the given function type.
inbuiltKnown :: Inbuilt -> Type' -> Builder Known
inbuiltKnown inbuilt fnTy = do
  t <- canonType fnTy
  (argTy, retTy) <- case view value t of
    TypeFn a r -> return (a, r)
    _          -> codegenError ("inbuilt " ++ show inbuilt ++ " at non-function type " ++ typeName t)
  cachedWith inbuiltFns (inbuilt, t) ("inbuilt " ++ show inbuilt) (\name -> Known name argTy retTy) $ \name -> do
    at <- lowerType argTy
    rt <- lowerType retTy
    defineFunction name rt [at] $ \[a] -> do
      r <- body inbuilt argTy retTy a
      terminate (Ret r)
    return (Known name argTy retTy)

-- | The body of an inbuilt, given its argument.
body :: Inbuilt -> Type' -> Type' -> Operand -> Builder Operand
body inbuilt argTy retTy a = case inbuilt of

  InbuiltAdd      -> arith "add"
  InbuiltSubtract -> arith "sub"
  InbuiltMultiply -> arith "mul"
  InbuiltNegate   -> let Op ty _ = a in instr ty (Arith "sub" (intConst ty 0) a)

  InbuiltEq  -> compare "eq" "eq"
  InbuiltNeq -> compare "ne" "ne"
  InbuiltLt  -> compare "slt" "ult"
  InbuiltGt  -> compare "sgt" "ugt"
  InbuiltLte -> compare "sle" "ule"
  InbuiltGte -> compare "sge" "uge"

  InbuiltNot -> instr i1 (Arith "xor" a (boolConst True))
  InbuiltOr  -> do { (x, y) <- unpair a; instr i1 (Arith "or" x y) }
  InbuiltAnd -> do { (x, y) <- unpair a; instr i1 (Arith "and" x y) }

  InbuiltGetInt -> do
    let Just (w, _) = intInfo (conName retTy)
    r <- runtimeCall "praxis_get_int" i64 []
    if w == 64 then return r else instr (I w) (Cast "trunc" r (I w))

  InbuiltPutInt -> do
    let Just (w, signed) = intInfo (conName argTy)
    x <- if w == 64 then return a else instr i64 (Cast (if signed then "sext" else "zext") a i64)
    runtimeCall_ (if signed then "praxis_put_int" else "praxis_put_uint") [x]
    return unitConst

  InbuiltGetStr   -> runtimeCall "praxis_get_str" Ptr []
  InbuiltPutStr   -> runtimeCall_ "praxis_put_str" [a] >> return unitConst
  InbuiltPutStrLn -> runtimeCall_ "praxis_put_str_ln" [a] >> return unitConst

  InbuiltPrint -> do
    showValue argTy a
    nl <- cString "\n"
    runtimeCall_ "praxis_show_lit" [nl]
    return unitConst

  InbuiltCompose -> do
    -- (b -> c, a -> b) -> a -> c
    let (_ :< TypePair fTy gTy) = argTy
        (_ :< TypeFn aTy bTy) = gTy
        (_ :< TypeFn _ cTy) = fTy
    (f, g) <- unpair a
    impl <- composeImpl fTy gTy aTy bTy cTy
    makeClosure impl [(fTy, f), (gTy, g)]

  InbuiltNewArray -> do
    -- (USize, () -> a) -> Array a
    let (_ :< TypeApply _ elemTy) = retTy
    (n, initFn) <- unpair a
    et <- lowerType elemTy
    bytes <- instr i64 (Arith "mul" n (intConst i64 (toInteger (sizeOf et))))
    size <- instr i64 (Arith "add" bytes (intConst i64 8))
    arr <- runtimeCall "praxis_alloc" Ptr [size]
    instr_ (Store n arr)
    forLoop n $ \i -> do
      e <- callClosureBorrowed elemTy initFn unitConst
      p <- elemPtr et arr i
      instr_ (Store e p)
    release initFn
    return arr

  InbuiltAtArray -> do
    -- (&r Array a, USize) -> &r a
    let (_ :< TypePair arrTy _) = argTy
        (_ :< TypeApply _ elemTy) = stripRef arrTy
    (arr, i) <- unpair a
    et <- lowerType elemTy
    boundsCheck arr i
    p <- elemPtr et arr i
    e <- instr et (Load et p)
    copyValue retTy e

  InbuiltLenArray -> instr i64 (Load i64 a)

  InbuiltSetArray -> do
    -- (Array a, USize, a) -> Array a
    let (_ :< TypeApply _ elemTy) = retTy
    (arr, rest) <- unpair a
    (i, e) <- unpair rest
    et <- lowerType elemTy
    boundsCheck arr i
    p <- elemPtr et arr i
    old <- instr et (Load et p)
    dropValue elemTy old
    instr_ (Store e p)
    return arr

  InbuiltCopy -> copyValue argTy a
  InbuiltDrop -> dropValue argTy a >> return unitConst

  where
    arith op = do
      (x, y) <- unpair a
      let Op ty _ = x
      instr ty (Arith op x y)

    compare signedOp unsignedOp = do
      (x, y) <- unpair a
      let (_ :< TypePair (_ :< TypeCon n) _) = argTy
          Just (_, signed) = intInfo n
      instr i1 (ICmp (if signed then signedOp else unsignedOp) x y)

    conName ty = case view value ty of
      TypeCon n -> n
      _         -> error "inbuilt: expected a type constructor"

    stripRef ty = case view value ty of
      TypeApplyOp _ t -> t
      _               -> ty

unpair :: Operand -> Builder (Operand, Operand)
unpair v = do
  let Op (Struct [ta, tb]) _ = v
  x <- instr ta (ExtractValue v [0])
  y <- instr tb (ExtractValue v [1])
  return (x, y)

elemPtr :: Ty -> Operand -> Operand -> Builder Operand
elemPtr et arr i = instr Ptr (GEP (Struct [i64, Arr 0 et]) arr [intConst i32 0, intConst i32 1, i])

boundsCheck :: Operand -> Operand -> Builder ()
boundsCheck arr i = do
  len <- instr i64 (Load i64 arr)
  ok <- instr i1 (ICmp "ult" i len)
  okL <- freshLabel "inbounds"
  failL <- freshLabel "outofbounds"
  terminate (CondBr ok okL failL)
  newBlock failL
  abort "array index out of bounds"
  newBlock okL

-- | The function underlying a composed closure: @((f, g), x) -> f (g x)@.
composeImpl :: Type' -> Type' -> Type' -> Type' -> Type' -> Builder Known
composeImpl fTy gTy aTy bTy cTy = do
  let implTy = phantom (TypeFn (phantom (TypePair (phantom (TypePair fTy gTy)) aTy)) cTy)
      argTy = phantom (TypePair (phantom (TypePair fTy gTy)) aTy)
  cachedWith inbuiltFns (InbuiltCompose, implTy) "compose" (\name -> Known name argTy cTy) $ \name -> do
    at <- lowerType argTy
    rt <- lowerType cTy
    defineFunction name rt [at] $ \[arg] -> do
      (fg, x) <- unpair arg
      (f, g) <- unpair fg
      y <- callClosure bTy g x
      z <- callClosure cTy f y
      terminate (Ret z)
    return (Known name argTy cTy)
