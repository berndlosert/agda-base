{-# OPTIONS --type-in-type #-}

module Notation.Sub where

-- Allows use to use - for subtraction.
record Sub (X : Set) : Set where
  constructor Sub:
  infixr 24 _-_
  field _-_ : X -> X -> X 

open Sub {{...}} public
