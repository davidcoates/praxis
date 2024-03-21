{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}

module Parse.Mixfix
( parse
)
where

import           Common              hiding (asum)
import           Praxis
import           Print
import           Term                hiding (Derivation)

import           Data.Array          (bounds, elems, listArray)
import qualified Data.Array          as Array
import           Data.Foldable       (asum)
import           Data.Graph          (Graph, reachable)
import           Data.Map.Strict     (Map)
import qualified Data.Map.Strict     as Map

import           Control.Applicative (Alternative (..))

-- Helper for parsing mixfix operators, respecting associativity and the precedence graph

newtype Parser a = Parser { runParser :: [Annotated Tok] -> [(a, [Annotated Tok])] }

eof :: Parser ()
eof = Parser $ \ts -> case ts of
  [] -> [((), [])]
  _  -> []

match :: (Annotated Tok -> Maybe a) -> Parser a
match f = Parser $ \ts -> case ts of
  (t:ts) -> case f t of
    Just a  -> [(a, ts)]
    Nothing -> []
  []     -> []

instance Functor Parser where
  fmap f p = Parser $ \ts -> [ (f x, ts') | (x, ts') <- runParser p ts ]

instance Applicative Parser where
  pure x = Parser $ \ts -> [ (x, ts) ]
  p <*> q = Parser $ \ts -> [ (f x, ts'') | (f, ts') <- runParser p ts, (x, ts'') <- runParser q ts' ]

instance Alternative Parser where
  empty = Parser $ \ts -> []
  a <|> b = Parser $ \ts -> runParser a ts ++ runParser b ts

run :: Source -> Parser (Annotated Exp) -> [Annotated Tok] -> Praxis (Annotated Exp)
run s p ts = case runParser (p <* eof) ts of
  []        -> throwAt s "no mixfix parse"
  [(a, [])] -> return a
  (a:b:_)   -> throwAt s "ambiguous mixfix parse" -- TODO provide more information here, say the first two parses?

-- The transitive closure of a precedence graph
closure :: Graph -> Graph
closure g = listArray (bounds g) (map (concatMap (reachable g)) (elems g))

parse :: Source -> [Annotated Tok] -> Praxis (Annotated Exp)
parse s ts = do
  opLevels <- use (opContext . levels)
  opDefns <- use (opContext . defns)
  opPrec <- use (opContext . prec)
  run s (mixfix opDefns opLevels (closure opPrec)) ts -- TODO skip the closure?

anyExp :: Parser (Annotated Exp)
anyExp = match f where
  f (_ :< TExp e) = Just e
  f _             = Nothing

namedOp :: Name -> Parser Name
namedOp n = match f where
  f (_ :< TOp m) = if m == n then Just n else Nothing
  f _            = Nothing

mixfix :: OpDefns -> [[Op]] -> Graph -> Parser (Annotated Exp)
mixfix defns levels prec = exp where

  nodes = [0 .. length levels - 1]

  exp :: Parser (Annotated Exp)
  exp = asum (map top nodes) <|> anyExp

  top :: Int -> Parser (Annotated Exp)
  top n = (op n Closed <*> pure []) <|>
          ((\a f b -> f [a, b]) <$> higher n <*> op n (Infix Nothing) <*> higher n) <|>
          (foldRight <$> some (right n) <*> higher n) <|>
          (foldLeft <$> higher n <*> some (left n))

  foldRight :: [Annotated Exp -> Annotated Exp] -> Annotated Exp -> Annotated Exp
  foldRight [f] e    = f e
  foldRight (f:fs) e = f (foldRight fs e)

  foldLeft :: Annotated Exp -> [Annotated Exp -> Annotated Exp] -> Annotated Exp
  foldLeft e [f]    = f e
  foldLeft e (f:fs) = foldLeft (f e) fs

  right :: Int -> Parser (Annotated Exp -> Annotated Exp)
  right n = ((\f x -> f [x]) <$> op n Prefix) <|>
            ((\x f y -> f [x, y]) <$> higher n <*> op n (Infix (Just AssocRight)))

  left :: Int -> Parser (Annotated Exp -> Annotated Exp)
  left n = ((\f x -> f [x]) <$> op n Postfix) <|>
           ((\f x y -> f [y, x]) <$> op n (Infix (Just AssocLeft)) <*> higher n)

  higher :: Int -> Parser (Annotated Exp)
  higher n = asum (map top (prec Array.! n)) <|> anyExp

  op :: Int -> Fixity -> Parser ([Annotated Exp] -> Annotated Exp)
  op n fixity = asum [ middle op | op <- levels !! n, fixity == snd (defns Map.! op) ]

  middle :: Op -> Parser ([Annotated Exp] -> Annotated Exp)
  middle op@(Op ps) = let (name, fixity) = defns Map.! op in (<$> parts (trim fixity ps)) $ \ps -> case fixity of
    Infix _ -> \[x,y] -> build name (x : ps ++ [y])
    Prefix  -> \[y]   -> build name (ps ++ [y])
    Postfix -> \[x]   -> build name (x : ps)
    Closed  -> \[]    -> build name ps

  build :: Name -> [Annotated Exp] -> Annotated Exp
  build n es = let es' = fold es in (view source es', Nothing) :< Apply (phantom $ Var n) es'

  fold :: [Annotated Exp] -> Annotated Exp
  fold = \case
    []     -> phantom Unit
    [e]    -> e
    (e:es) -> let es' = fold es in (view source e <> view source es', Nothing) :< Pair e es'

  trim :: Fixity -> [Maybe Name] -> [Maybe Name]
  trim = \case
    Infix _ -> tail . init
    Prefix  -> init
    Postfix -> tail
    Closed  -> id

  parts :: [Maybe Name] -> Parser [Annotated Exp]
  parts = \case
    []             -> pure []
    (Just n  : ps) -> namedOp n *> parts ps
    (Nothing : ps) -> (:) <$> anyExp <*> parts ps
