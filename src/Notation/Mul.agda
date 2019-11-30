{-# OPTIONS --type-in-type #-}

module Notation.Mul where

-- Allows us to use ``*`` or ``×`` to form products.
record Mul (X : Set) : Set where
  constructor Mul:
  infixr 25 _*_ _×_
  field _*_ : X -> X -> X
  _×_ = _*_

open Mul {{...}} public
