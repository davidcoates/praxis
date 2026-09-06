{-# LANGUAGE TemplateHaskell #-}

-- | The code generation monad: a state over 'Praxis' holding the function under construction, the module built so
-- far, the layout of the program's data types, and caches of generated helper functions.
module Codegen.Builder
  ( Builder
  , Type'
  , State
  , emptyState
  , runBuilder

  , DataInfo(..)
  , ConInfo(..)
  , Known(..)

  -- * Lenses
  , dataTypes
  , enums
  , conInfos
  , enumCons
  , knownFns
  , globalVals
  , isCopy
  , copyFns
  , dropFns
  , showFns
  , thunks
  , statics
  , dropEnvs
  , inbuiltFns
  , strings

  -- * Building
  , fresh
  , freshLabel
  , instr
  , instr_
  , terminate
  , newBlock
  , currentBlock
  , defineFunction
  , defineExported
  , prependInstr
  , addGlobal
  , declare
  , runtimeCall
  , runtimeCall_
  , cached
  , cachedWith
  , codegenError
  , symbolOf
  ) where

import           Codegen.IR
import           Common
import           Praxis                    hiding (fresh)
import           Stage
import           Term                      hiding (Op)

import           Control.Lens              (Lens', makeLenses)
import           Control.Monad.Trans       (lift)
import qualified Control.Monad.Trans.State as S
import           Data.Map.Strict           (Map)
import qualified Data.Map.Strict           as Map
import           Data.Set                  (Set)
import qualified Data.Set                  as Set
import           Prelude                   hiding (null)


type Type' = Annotated TypeCheck Type

-- | A (monomorphic) data type: its constructors in tag order, with their payload types.
data DataInfo = DataInfo
  { dataMode :: DataMode
  , dataCons :: [(Name, Type')]
  }

-- | A data constructor: the data type it belongs to, and its tag.
data ConInfo = ConInfo
  { conData :: Name
  , conTag  :: Int
  }

-- | A known (top-level) function: its symbol, argument type and return type.
data Known = Known
  { knownSym :: String
  , knownArg :: Type'
  , knownRet :: Type'
  }

data State = State
  { _counter    :: Int
  , _current    :: Maybe (String, [(Maybe String, Instr)])
  -- ^ The block under construction: its label and its instructions (reversed)
  , _blocks     :: [Block]
  -- ^ Completed blocks of the function under construction (reversed)
  , _functions  :: [Function]
  , _globals    :: [Global]
  , _declared   :: Set String
  , _dataTypes  :: Map Name DataInfo
  , _enums      :: Map Name [Name]
  , _dataConMap :: Map Name ConInfo
  , _enumConMap :: Map Name (Name, Int)
  , _knownFns   :: Map Name Known
  , _globalVals :: Map Name (String, Type')
  , _isCopy     :: Type' -> Bool
  , _copyFns    :: Map Type' String
  , _dropFns    :: Map Type' String
  , _showFns    :: Map Type' String
  , _thunks     :: Map (String, [Type']) String
  , _statics    :: Map String String
  , _dropEnvs   :: Map [Type'] String
  , _inbuiltFns :: Map (Inbuilt, Type') Known
  , _strings    :: Map String String
  }

makeLenses ''State

-- Naming: the constructor maps are exported under friendlier names.
conInfos :: Lens' State (Map Name ConInfo)
conInfos = dataConMap

enumCons :: Lens' State (Map Name (Name, Int))
enumCons = enumConMap

emptyState :: State
emptyState = State
  { _counter    = 0
  , _current    = Nothing
  , _blocks     = []
  , _functions  = []
  , _globals    = []
  , _declared   = Set.empty
  , _dataTypes  = Map.empty
  , _enums      = Map.empty
  , _dataConMap = Map.empty
  , _enumConMap = Map.empty
  , _knownFns   = Map.empty
  , _globalVals = Map.empty
  , _isCopy     = const False
  , _copyFns    = Map.empty
  , _dropFns    = Map.empty
  , _showFns    = Map.empty
  , _thunks     = Map.empty
  , _statics    = Map.empty
  , _dropEnvs   = Map.empty
  , _inbuiltFns = Map.empty
  , _strings    = Map.empty
  }

type Builder = StateT State Praxis

-- | Run a builder, returning the module it built.
runBuilder :: Builder () -> State -> Praxis Module
runBuilder b s = do
  ((), s') <- S.runStateT b s
  return (Module (reverse (view globals s')) (reverse (view functions s')))

codegenError :: String -> Builder a
codegenError msg = lift (throw Codegen msg)


-- * Fresh names

fresh :: Builder String
fresh = do
  n <- use counter
  counter .= n + 1
  return ("t" ++ show n)

freshLabel :: String -> Builder String
freshLabel hint = do
  n <- use counter
  counter .= n + 1
  return (hint ++ "." ++ show n)

-- | The symbol of a Praxis top-level name.
symbolOf :: Name -> String
symbolOf (Name s (Unique u)) = "p." ++ s ++ (if u == 0 then "" else "." ++ show u)


-- * Blocks

-- | Emit an instruction with a result of the given type.
instr :: Ty -> Instr -> Builder Operand
instr ty i = do
  name <- fresh
  emit (Just name, i)
  return (Op ty (Local name))

-- | Emit an instruction with no result.
instr_ :: Instr -> Builder ()
instr_ i = emit (Nothing, i)

emit :: (Maybe String, Instr) -> Builder ()
emit i = use current >>= \case
  Nothing           -> codegenError "internal: instruction emitted outside of a block"
  Just (label, is)  -> current .= Just (label, i : is)

-- | End the current block.
terminate :: Terminator -> Builder ()
terminate t = use current >>= \case
  Nothing          -> codegenError "internal: terminator emitted outside of a block"
  Just (label, is) -> do
    blocks %= (Block label (reverse is) t :)
    current .= Nothing

-- | Start a new block with the given label.
newBlock :: String -> Builder ()
newBlock label = use current >>= \case
  Nothing -> current .= Just (label, [])
  Just _  -> codegenError "internal: block started while another is open"

-- | The label of the current block.
currentBlock :: Builder String
currentBlock = use current >>= \case
  Nothing         -> codegenError "internal: no current block"
  Just (label, _) -> return label


-- * Functions and globals

-- | Define a (private) function. The body receives the parameters, and must terminate every block it opens.
defineFunction :: String -> Ty -> [Ty] -> ([Operand] -> Builder ()) -> Builder ()
defineFunction = defineFunctionWith True

-- | Define a function which is visible to the runtime.
defineExported :: String -> Ty -> [Ty] -> ([Operand] -> Builder ()) -> Builder ()
defineExported = defineFunctionWith False

defineFunctionWith :: Bool -> String -> Ty -> [Ty] -> ([Operand] -> Builder ()) -> Builder ()
defineFunctionWith private name ret paramTys body = do
  savedCurrent <- use current
  savedBlocks <- use blocks
  current .= Nothing
  blocks .= []
  params <- mapM (\ty -> (ty,) <$> fresh) paramTys
  newBlock "entry"
  body [ Op ty (Local p) | (ty, p) <- params ]
  use current >>= \case
    Nothing -> return ()
    Just _  -> codegenError ("internal: function " ++ name ++ " does not end with a terminator")
  bs <- use blocks
  functions %= (Function name ret params (reverse bs) private :)
  current .= savedCurrent
  blocks .= savedBlocks

-- | Insert an instruction at the start of a completed block of the function under construction (for phis whose
-- incoming edges are only known after the block is complete).
prependInstr :: String -> (Maybe String, Instr) -> Builder ()
prependInstr label i = blocks %= map patch where
  patch b | blockLabel b == label = b { blockInstrs = i : blockInstrs b }
          | otherwise             = b

addGlobal :: Global -> Builder ()
addGlobal g = globals %= (g :)

-- | Declare an external (runtime) function, once.
declare :: String -> Ty -> [Ty] -> Builder ()
declare name ret params = do
  seen <- use declared
  unless (name `Set.member` seen) $ do
    declared %= Set.insert name
    addGlobal (Declare name ret params)

-- | Call a runtime function.
runtimeCall :: String -> Ty -> [Operand] -> Builder Operand
runtimeCall name ret args = do
  declare name ret [ ty | Op ty _ <- args ]
  instr ret (Call ret (global name) args)

runtimeCall_ :: String -> [Operand] -> Builder ()
runtimeCall_ name args = do
  declare name Void [ ty | Op ty _ <- args ]
  instr_ (Call Void (global name) args)

-- | Look up a generated helper by key, generating it under a fresh symbol if it is missing. The symbol is registered
-- before the generator runs, so recursive helpers can refer to themselves.
cached :: Ord k => Lens' State (Map k String) -> k -> String -> (String -> Builder ()) -> Builder String
cached l key hint gen = cachedWith l key hint id (\name -> gen name >> return name)

-- | Like 'cached', but the cache holds a value derived from the symbol.
cachedWith :: Ord k => Lens' State (Map k v) -> k -> String -> (String -> v) -> (String -> Builder v) -> Builder v
cachedWith l key hint mkPlaceholder gen = do
  m <- use l
  case Map.lookup key m of
    Just v  -> return v
    Nothing -> do
      n <- use counter
      counter .= n + 1
      let name = hint ++ "." ++ show n
      l %= Map.insert key (mkPlaceholder name)
      v <- gen name
      l %= Map.insert key v
      return v
