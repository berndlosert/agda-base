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
  item s = case String.toList s of \ where
    [] -> []
    (c :: cs) -> [ Pair: c (String.fromList cs) ]
