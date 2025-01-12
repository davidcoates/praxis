{-# LANGUAGE DataKinds #-}

module Parse.Mixfix
  ( parse
  ) where

import           Common              hiding (asum)
import           Parse.State
import           Praxis
import           Print
import           Stage
import           Term

import           Data.Array          (bounds, elems, listArray)
import qualified Data.Array          as Array
import           Data.Foldable       (asum)
import           Data.Graph          (Graph, Vertex, reachable, vertices)
import           Data.Map.Strict     (Map)
import qualified Data.Map.Strict     as Map

import           Control.Applicative (Alternative (..))


-- Helper for parsing mixfix operators, respecting associativity and the precedence graph

newtype Parser a = Parser { runParser :: [Annotated Initial Tok] -> [(a, [Annotated Initial Tok])] }

eof :: Parser ()
eof = Parser $ \ts -> case ts of
  [] -> [((), [])]
  _  -> []

match :: (Annotated Initial Tok -> Maybe a) -> Parser a
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

run :: Source -> Parser (Annotated Initial Exp) -> [Annotated Initial Tok] -> Praxis (Annotated Initial Exp)
run src exp ts = case runParser (exp <* eof) ts of
  []        -> throwAt Parse src "no mixfix parse"
  [(a, [])] -> return a
  (a:b:_)   -> throwAt Parse src "ambiguous mixfix parse" -- TODO provide more information here, say the first two parses?

-- The transitive closure of a precedence graph
closure :: Graph -> Graph
closure g = listArray (bounds g) (map (concatMap (reachable g)) (elems g))

parse :: Source -> [Annotated Initial Tok] -> Praxis (Annotated Initial Exp)
parse src ts = do
  opNodes <- use (parseState . opState . nodes)
  opDefinitions <- use (parseState . opState . definitions)
  opPrecedence <- use (parseState . opState . precedence)
  run src (mixfix opDefinitions opNodes (closure opPrecedence)) ts -- TODO skip the closure?

anyExp :: Parser (Annotated Initial Exp)
anyExp = match f where
  f (_ :< TokExp e) = Just e
  f _               = Nothing

namedOp :: Name -> Parser Source
namedOp n = match f where
  f ((src, _) :< TokOp m) = if m == n then Just src else Nothing
  f _                     = Nothing

mixfix :: OpDefinitions -> OpNodes -> Graph -> Parser (Annotated Initial Exp)
mixfix definitions nodes precedence = exp where

  exp :: Parser (Annotated Initial Exp)
  exp = asum (map top (vertices precedence)) <|> anyExp

  top :: Vertex -> Parser (Annotated Initial Exp)
  top n =
    (op n Closed <*> pure []) <|>
    ((\a f b -> f [a, b]) <$> higher n <*> op n (Infix Nothing) <*> higher n) <|>
    (foldRight <$> some (right n) <*> higher n) <|>
    (foldLeft <$> higher n <*> some (left n))

  foldRight :: [Annotated Initial Exp -> Annotated Initial Exp] -> Annotated Initial Exp -> Annotated Initial Exp
  foldRight [f] e    = f e
  foldRight (f:fs) e = f (foldRight fs e)

  foldLeft :: Annotated Initial Exp -> [Annotated Initial Exp -> Annotated Initial Exp] -> Annotated Initial Exp
  foldLeft e [f]    = f e
  foldLeft e (f:fs) = foldLeft (f e) fs

  right :: Vertex -> Parser (Annotated Initial Exp -> Annotated Initial Exp)
  right n =
    ((\f x -> f [x]) <$> op n Prefix) <|>
    ((\x f y -> f [x, y]) <$> higher n <*> op n (Infix (Just AssocRight)))

  left :: Vertex -> Parser (Annotated Initial Exp -> Annotated Initial Exp)
  left n =
    ((\f x -> f [x]) <$> op n Postfix) <|>
    ((\f x y -> f [y, x]) <$> op n (Infix (Just AssocLeft)) <*> higher n)

  higher :: Vertex -> Parser (Annotated Initial Exp)
  higher n = asum (map top (precedence Array.! n)) <|> anyExp

  op :: Vertex -> Fixity -> Parser ([Annotated Initial Exp] -> Annotated Initial Exp)
  op n fixity = asum [ middle op | op <- nodes !! n, fixity == snd (definitions Map.! op) ]

  middle :: Annotated Parse Op -> Parser ([Annotated Initial Exp] -> Annotated Initial Exp)
  middle op@(_ :< Op ps) = let (name, fixity) = definitions Map.! op in (<$> parts (trim fixity ps)) $ \(src, ps) -> case fixity of
    Infix _ -> \[x,y] -> build src name (x : ps ++ [y])
    Prefix  -> \[y]   -> build src name (ps ++ [y])
    Postfix -> \[x]   -> build src name (x : ps)
    Closed  -> \[]    -> build src name ps

  build :: Source -> Name -> [Annotated Initial Exp] -> Annotated Initial Exp
  build src name es = let es' = fold src es in (view source es', Nothing) :< Apply ((src, Nothing) :< Var name) es'

  fold :: Source -> [Annotated Initial Exp] -> Annotated Initial Exp
  fold src = \case
    []     -> (src, Nothing) :< Unit
    [e]    -> e
    (e:es) -> let es' = fold src es in (view source e <> view source es', Nothing) :< Pair e es'

  trim :: Fixity -> [Maybe Name] -> [Maybe Name]
  trim = \case
    Infix _ -> tail . init
    Prefix  -> init
    Postfix -> tail
    Closed  -> id

  parts :: [Maybe Name] -> Parser (Source, [Annotated Initial Exp])
  parts = \case
    []             -> pure (Phantom, [])
    (Just n : ps)  -> (\s1 (s2, es) -> (s1 <> s2, es)) <$> namedOp n <*> parts ps
    (Nothing : ps) -> (\e (s, es) -> (s, e:es)) <$> anyExp <*> parts ps
