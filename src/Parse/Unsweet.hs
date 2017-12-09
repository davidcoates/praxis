module Parse.Unsweet
  (parse, Expr(..), Lit(..), Op(..))
where

import qualified Parse.Sweet as Sweet
import Text.Parsec.Error (ParseError)
import Text.Parsec.Prim hiding (parse)
import Text.Parsec.Combinator
import qualified Data.Map.Strict as Map
import Data.Map (Map)

data Lit = Integer Integer
         deriving (Show)

data Op = Plus | Eq | User String
  deriving (Show, Ord, Eq)

-- data Binding = Binding String Expr
 --            deriving (Show)

data Expr = Lit Lit
--          | Let Binding Expr
--          | If Expr Expr Expr
          | Prim Op Expr Expr -- Eventually replace this with function application
          deriving (Show)

desugarLit :: Sweet.Lit -> Lit
desugarLit (Sweet.Integer n) = Integer n

desugarOp :: Sweet.Op -> Op
desugarOp Sweet.Plus = Plus
desugarOp Sweet.Eq   = Eq

data Assoc = Leftfix | Rightfix | Nonfix deriving Eq
type Fixity = (Int, Assoc)

opTable :: Map Op Fixity
opTable = Map.fromList [(Plus, (6, Leftfix)), (Eq, (4, Nonfix)), (User "", (-1, Nonfix))]

desugarExpr :: Sweet.Expr -> Expr
desugarExpr (Sweet.Lit lit) = Lit (desugarLit lit)
desugarExpr (Sweet.OpSequence es os) = case resolve opTable (map desugarExpr es) (map desugarOp os) of Just x -> x

resolve :: Map Op Fixity -> [Expr] -> [Op] -> Maybe Expr 
resolve fixity es os = fst <$> parse (User "":os) es
  where  
    parse :: [Op] -> [Expr] -> Maybe (Expr, ([Op], [Expr]))  
    parse _  [e] = Just (e, ([],[]))
    parse (op1:op2:ops) (e:es)
       -- case (1): check for illegal expressions  
       | prec1 == prec2 && (fix1 /= fix2 || fix1 == Nonfix)  
       = Nothing  
 
       -- case (2): op1 and op2 should associate to the left  
       | prec1 > prec2 || (prec1 == prec2 && fix1 == Leftfix)  
       = Just (e, (op2:ops, es))
 
       -- case (3): op1 and op2 should associate to the right  
       | otherwise  
       = do (r, (ops', es')) <- parse (op2:ops) es  
            parse (op1:ops') (Prim op2 e r : es')  
         where (prec1, fix1) = fixity Map.! op1
               (prec2, fix2) = fixity Map.! op2 

parse :: String -> Either ParseError Expr
parse s = desugarExpr <$> Sweet.parse s

