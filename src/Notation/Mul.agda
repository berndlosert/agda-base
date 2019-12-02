{-# OPTIONS --type-in-type #-}

module Notation.Mul where

-- Instances of Mul will allow us to use _*_ to form products.

record Mul (X : Set) : Set where
  constructor Mul:
  infixr 25 _*_
  field
    _*_ : X -> X -> X

open Mul {{...}} public
