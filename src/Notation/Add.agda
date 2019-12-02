{-# OPTIONS --type-in-type #-}

module Notation.Add where

-- Allows us to use + to form various kinds of sums.
record Add (X : Set) : Set where
  constructor Add:
  infixr 24 _+_
  field _+_ : X -> X -> X

open Add {{...}} public
