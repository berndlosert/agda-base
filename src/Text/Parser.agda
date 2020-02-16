{-# OPTIONS --type-in-type #-}

module Text.Parser where

-- Parser that parses values of type X from a string.

open import Data.List
open import Data.String
open import Data.Pair

Parser : Set -> Set
Parser X = String -> List (X * String)

-- Parser is a functor.

open import Data.Functor

instance
  Functor:Parser : Endofunctor Sets Parser
  Functor:Parser .map f p s = map (cross f id) (p s)

-- Parser is a monad.

open import Control.Monad
open import Data.Function

instance
  Monad:Parser : Monad Sets Parser
  Monad:Parser .return x s = [ Pair: x s ]
  Monad:Parser .extend f p s = List.concat $ map (uncurry f) (p s)

-- Parser is an applicative functor.

open import Control.Applicative

instance
  Applicative:Parser : Applicative Parser
  Applicative:Parser = Applicative: ap return

-- Parser is an alternative functor.

instance
  Alternative:Parser : Alternative Parser
  Alternative:Parser ._<|>_ p q s = p s <|> q s
  Alternative:Parser .empty s = empty

module Parser where

  -- item is a parser that consumes the first character if the input string is
  -- nonempty, and fails otherwise.

  open import Data.Char

  item : Parser Char
  item = List.fromMaybe <<< String.uncons

  -- first p is the parser whose output contains only the first successful
  -- parse (if it has one at all).

  first : forall {X} -> Parser X -> Parser X
  first p s = case p s of \ where
    [] -> []
    (x :: _) -> [ x ]

  -- plus p q is just <|> wrapped in first.
  plus : forall {X} -> Parser X -> Parser X -> Parser X
  plus p q = first (p <|> q)

  -- satisfy takes a predicate, and yields a parser that consumes a single
  -- character if it satisfies the predicate, and fails otherwise.

  satisfy : (Char -> Bool) -> Parser Char
  satisfy p = do
    c <- item
    guard (p c)
    return c

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

  open import Data.Maybe

  {-# TERMINATING #-}
  string : String -> Parser String
  string s = case String.uncons s of \ where
    nothing -> return ""
    (just (Pair: c s')) -> char c >> string s' >> return (String.cons c s')

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

  open import Data.Nat

  nat : Parser Nat
  nat = chainl1
      (digit >>= \ x -> return (ord x - ord '0'))
      (return (\ m n -> 10 * m + n))
