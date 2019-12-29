{-# OPTIONS --type-in-type #-}

module Notation.Negative where

-- This allows us to define what the syntax -n means when n
-- is a number literal.

open import Agda.Builtin.FromNeg public

-- And this allows us to define negation as an operation.

record Negation (X : Set) : Set where
  constructor Negation:
  field
    -_ : X -> X

open Negation {{...}} public
