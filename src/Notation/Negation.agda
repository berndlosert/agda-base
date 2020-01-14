{-# OPTIONS --type-in-type #-}

module Notation.Negation where

-- This allows us to define negation as an operation.

record Negation (X : Set) : Set where
  constructor Negation:
  field -_ : X -> X

open Negation {{...}} public
