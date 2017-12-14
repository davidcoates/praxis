module Parse.Unsweet
  (parse, Exp(..), Lit(..), Op(..))
where

import qualified Parse.Sweet as Sweet
import Parse.Sweet (Op, Tok(..))
import Text.Parsec.Error (ParseError)
import Text.Parsec.Prim hiding (parse)
import Text.Parsec.Combinator
import qualified Data.Map.Strict as Map
import Data.Map (Map)
import Control.Monad (guard)
import AST

-- data Binding = Binding String Exp
 --            deriving (Show)


data Assoc = Leftfix | Rightfix | Nonfix deriving Eq
type Fixity = (Int, Assoc)

opTable :: Map Op Fixity
opTable = Map.fromList [("+", (6, Leftfix)), ("==", (4, Nonfix))]

desugarExp :: Praxis Sweet.Exp -> Praxis Exp
desugarExp (_ :< Sweet.Infix ts) = case resolve opTable ts of Just x -> x
desugarExp (a :< x) = a :< desugarExp' x
  where desugarExp' (Sweet.Lit lit)     = Lit lit
        desugarExp' (Sweet.If e1 e2 e3) = If (desugarExp e1) (desugarExp e2) (desugarExp e3)

resolve :: Map Op Fixity -> [Praxis Tok] -> Maybe (Praxis Exp)
resolve fixity ts = fst <$> parseNeg ("", (-1, Nonfix)) ts
  where  
    parseNeg :: (Op, Fixity) -> [Praxis Tok] -> Maybe (Praxis Exp, [Praxis Tok])
    parseNeg op1 (_ :< TExp e1 : rest)
      = parse op1 (desugarExp e1) rest
    parseNeg op1 (p :< TNeg : rest)
      = do guard (prec1 < 6)
           (r, rest') <- parseNeg ("-", (6, Leftfix)) rest
           parse op1 (p :< Apply (p :< Prim Neg) r) rest'
      where
        (s1, (prec1, fix1)) = op1

    parse :: (Op, Fixity) -> Praxis Exp -> [Praxis Tok] -> Maybe (Praxis Exp, [Praxis Tok])
    parse _   e1 [] = Just (e1, [])  
    parse op1 e1 (p :< TOp s2 : rest)  
       -- case (1): check for illegal expressions  
       | prec1 == prec2 && (fix1 /= fix2 || fix1 == Nonfix)  
       = Nothing  
 
       -- case (2): op1 and op2 should associate to the left  
       | prec1 > prec2 || (prec1 == prec2 && fix1 == Leftfix)  
       = Just (e1, p :< TOp s2 : rest)  
 
       -- case (3): op1 and op2 should associate to the right  
       | otherwise  
       = do (r, rest') <- parseNeg op2 rest  
            parse op1 (p :< Apply (p :< Apply (p :< Fun s2) e1) r) rest'
       where  
        (_, (prec1, fix1))  = op1
        op2 = (s2, fixity Map.! s2)
        (_, (prec2, fix2)) = op2

parse :: String -> Either ParseError (Praxis Exp)
parse s = desugarExp <$> Sweet.parse s

