{-# OPTIONS --type-in-type #-}

module Notation.Div where

-- Allows us to use / for division on number types. 
record Div (X : Set) : Set where
  constructor Div:
  infixr 25 _/_
  field
    Constraint : X → Set
    _/_ : (x y : X) → {_ : Constraint y} → X

open Div {{...}} hiding (Constraint) public
