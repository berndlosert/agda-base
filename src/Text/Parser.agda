{-# OPTIONS --type-in-type #-}

module Text.Parser where

import Data.List as List
import Data.Maybe
import Data.Pair
import Data.String as String
import Prelude

open Data.Maybe using (maybeToList)
open Data.Pair using (cross)
open Prelude

-- Parser that parses values of type X from a string.
Parser : Set -> Set
Parser X = String -> List (X * String)

-- Parser is a functor.
instance
  Functor:Parser : Functor Sets Sets Parser
  Functor:Parser .map f p s = map (cross f id) (p s)

-- Parser is a monad.
instance
  Monad:Parser : Monad Sets Parser
  Monad:Parser .return x s = [ Pair: x s ]
  Monad:Parser .extend f p s = join $ map (uncurry f) (p s)

-- Parser is an applicative functor.
instance
  Applicative:Parser : Applicative Parser
  Applicative:Parser = Applicative: ap return

-- The empty parser doesn't parse anything.
empty : forall {X} -> Parser X
empty s = []

-- Given two parsers p, q : Parser X, p <|> q is the parser that
-- nondeterministically chooses between running p or running q.
_<|>_ : forall {X} -> Parser X -> Parser X -> Parser X
p <|> q = \ s -> p s ++ q s

-- item is a parser that consumes the first character if the input string is
-- nonempty, and fails otherwise.
item : Parser Char
item = maybeToList <<< String.uncons

-- first p is the parser whose output contains only the first successful
-- parse (if it has one at all).
first : forall {X} -> Parser X -> Parser X
first p s with p s
... | [] = []
... | (x :: _) = [ x ]

-- plus p q is just <|> wrapped in first.
plus : forall {X} -> Parser X -> Parser X -> Parser X
plus p q = first (p <|> q)

-- satisfy takes a predicate, and yields a parser that consumes a single
-- character if it satisfies the predicate, and fails otherwise.
satisfy : (Char -> Bool) -> Parser Char
satisfy p = do
  c <- item
  if p c then return c else empty

-- This combinator is used for creating single character parsers.
char : Char -> Parser Char
char c = satisfy (c ==_)

-- Parse digits.
digit : Parser Char
digit = satisfy isDigit

-- Parse letters.
letter : Parser Char
letter = satisfy isAlpha

-- Parse lower-case characters.
lower : Parser Char
lower = satisfy isLower

-- Parser upper-case characters.
upper : Parser Char
upper = satisfy (\ c -> isAlpha c && not (isLower c))

-- Parse alpha-numeric characters.
alphanum : Parser Char
alphanum = letter <|> digit

-- Parse words.
{-# TERMINATING #-}
word : Parser String
word = neword <|> return ""
  where
    neword : Parser String
    neword = do
      c <- letter
      s <- word
      return (String.cons c s)

-- Produce string parsers.
{-# TERMINATING #-}
string : String -> Parser String
string s with String.uncons s
... | nothing = return ""
... | (just (Pair: c s')) = char c >> string s' >> return (String.cons c s')

-- The combinator many (resp. many1) applies a parser p zero (resp. one) or
-- more times to an input string. The results from each application of p are
-- returned in a list.
{-# TERMINATING #-}
many : forall {x} -> Parser x -> Parser (List x)
many1 : forall {x} -> Parser x -> Parser (List x)

many p = plus (many1 p) (return [])
many1 p = do
  x <- p
  xs <- many p
  return (x :: xs)

-- This parses nonempty sequences of items separated by operators that
-- associate to the left.
{-# TERMINATING #-}
chainl1 : forall {X} -> Parser X -> Parser (X -> X -> X) -> Parser X
chainl1 p op = p >>= rest
  where
    rest : _
    rest x = plus
      (op >>= \ f -> p >>= \ y -> rest (f x y))
      (return x)

-- Parser for natural numbers.
nat : Parser Nat
nat = chainl1
    (digit >>= \ x -> return (ord x - ord '0'))
    (return (\ m n -> 10 * m + n))

-- Spaces parser.
spaces : Parser Unit
spaces = do
  many1 (satisfy isSpace)
  return tt

-- Junk parser.
junk : Parser Unit
junk = do
  many spaces
  return tt

-- Parser that skip junk.
skip : forall {X} -> Parser X -> Parser X
skip p = junk >> p
