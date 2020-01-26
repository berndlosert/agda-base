{-# OPTIONS --type-in-type #-}

module Text.Parser where

open import Data.List
open import Data.String

-- Parser of X values.

Parser : Set -> Set
Parser X = String -> List (X * String)

-- Returns the first object of the first parse.

parse : forall {X} -> Parser X -> String -> X
parse p s = fst (head (p s))
