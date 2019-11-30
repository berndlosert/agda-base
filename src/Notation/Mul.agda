{-# OPTIONS --type-in-type #-}

module Notation.Mul where

-- Allows us to use * to form products.
record Mul (X : Set) : Set where
  constructor Mul:
  infixr 25 _*_
  field _*_ : X -> X -> X

open Mul {{...}} public
