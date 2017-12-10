module Parse.Unsweet
  (parse, Exp(..), Lit(..), Op(..))
where

import qualified Parse.Sweet as Sweet
import Parse.Sweet (Op(..), Lit(..), Tok(..))
import Text.Parsec.Error (ParseError)
import Text.Parsec.Prim hiding (parse)
import Text.Parsec.Combinator
import qualified Data.Map.Strict as Map
import Data.Map (Map)
import Control.Monad (guard)

-- data Binding = Binding String Exp
 --            deriving (Show)

data Exp = Lit Lit
--          | Let Binding Exp
          | If Exp Exp Exp
          | Neg Exp
          | Prim Op Exp Exp -- Eventually replace this with function application
          deriving (Show, Eq)

data Assoc = Leftfix | Rightfix | Nonfix deriving Eq
type Fixity = (Int, Assoc)

opTable :: Map Op Fixity
opTable = Map.fromList [(Op "+", (6, Leftfix)), (Op "==", (4, Nonfix))]

desugarExp :: Sweet.Exp -> Exp
desugarExp (Sweet.Lit lit) = Lit lit
desugarExp (Sweet.OpSequence ts) = case resolve opTable ts of Just x -> x
desugarExp (Sweet.If e1 e2 e3) = If (desugarExp e1) (desugarExp e2) (desugarExp e3)

resolve :: Map Op Fixity -> [Sweet.Tok] -> Maybe Exp
resolve fixity ts = fst <$> parseNeg (Op "", (-1, Nonfix)) ts
  where  
    parseNeg :: (Op, Fixity) -> [Sweet.Tok] -> Maybe (Exp, [Sweet.Tok])
    parseNeg op1 (TExp e1 : rest)
      = parse op1 (desugarExp e1) rest
    parseNeg op1 (TNeg : rest)
      = do guard (prec1 < 6)
           (r, rest') <- parseNeg (Op "-", (6, Leftfix)) rest
           parse op1 (Neg r) rest'
      where
        (s1, (prec1, fix1)) = op1

    parse :: (Op, Fixity) -> Exp -> [Sweet.Tok] -> Maybe (Exp, [Sweet.Tok])
    parse _   e1 [] = Just (e1, [])  
    parse op1 e1 (TOp s2 : rest)  
       -- case (1): check for illegal expressions  
       | prec1 == prec2 && (fix1 /= fix2 || fix1 == Nonfix)  
       = Nothing  
 
       -- case (2): op1 and op2 should associate to the left  
       | prec1 > prec2 || (prec1 == prec2 && fix1 == Leftfix)  
       = Just (e1, TOp s2 : rest)  
 
       -- case (3): op1 and op2 should associate to the right  
       | otherwise  
       = do (r,rest') <- parseNeg op2 rest  
            parse op1 (Prim s2 e1 r) rest'
       where  
        (_, (prec1, fix1))  = op1
        op2 = (s2, fixity Map.! s2)
        (_, (prec2, fix2)) = op2

parse :: String -> Either ParseError Exp
parse s = desugarExp <$> Sweet.parse s

