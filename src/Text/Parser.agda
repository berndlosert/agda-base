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

private variable A : Set

record Parser (A : Set) : Set where
  constructor parser
  field
    runParser : String -> List (A * String)

open Parser public

instance
  functorParser : Functor Parser
  functorParser .map f p = parser \ s -> map (cross f id) (runParser p s)

  applicativeParser : Applicative Parser
  applicativeParser .pure x = parser \ s -> singleton (x , s)
  applicativeParser ._<*>_ f p = parser \ s -> do
    (g , s') <- runParser f s
    (x , s'') <- runParser p s'
    return (g x , s'')

  monadParser : Monad Parser
  monadParser ._>>=_ p f = parser \ s -> join $ do
    (v , s') <- (runParser p s)
    return $ runParser (f v) s'

  semigroupParser : Semigroup (Parser A)
  semigroupParser . _<>_ p q = parser \ s -> runParser p s ++ runParser q s

  monoidParser : Monoid (Parser A)
  monoidParser .empty = parser $ const []

-- item is a parser that consumes the first character if the input string is
-- nonempty, and fails otherwise.
item : Parser Char
item = parser (maybeToList <<< String.uncons)

-- first p is the parser whose output contains only the first successful
-- parse (if it has one at all).
first : Parser A -> Parser A
first p = parser \ s -> runParser p s # \ where
  [] -> []
  (x :: _) -> singleton x

-- plus p q is just <> wrapped in first.
plus : Parser A -> Parser A -> Parser A
plus p q = first (p <> q)

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
alphanum = letter <> digit

-- Parse words.
{-# TERMINATING #-}
word : Parser String
word = neword <> return ""
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
... | (just (c , s')) = char c >> string s' >> return (String.cons c s')

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
chainl1 : Parser A -> Parser (A -> A -> A) -> Parser A
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

-- Parser that skips junk.
skip : Parser A -> Parser A
skip p = junk >> p

-- Consumes input as long as the predicate returns true, and return the
-- consumed input.
takeWhile : (Char -> Bool) -> Parser String
takeWhile p = parser \ s ->
  singleton (String.takeWhile p s , String.dropWhile p s)

-- Consumes the rest of the input.
takeRest : Parser String
takeRest = takeWhile (const true)

-- Run a parser on a string and get the first result.
parse : Parser A -> String -> Maybe A
parse p s with runParser p s
... | [] = nothing
... | ((a , _) :: _) = just a
