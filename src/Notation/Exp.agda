{-# OPTIONS --type-in-type #-}

module Notation.Exp where

-- Use _^_ for writing exponentials of various sorts.

record Exp (X Y Z : Set) : Set where
  constructor Exp:
  infixr 50 _^_
  field
    _^_ : X -> Y -> Z

open Exp {{...}} public
