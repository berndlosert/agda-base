{-# OPTIONS --type-in-type #-}

module Notation.Mod where

-- Allows us to use % for defining mod on various number types.
record Mod (X : Set) : Set where
  constructor Mod:
  infixr 25 _%_
  field 
    Constraint : X → Set
    _%_ : (x y : X) → {_ : Constraint y} → X

open Mod {{...}} hiding (Constraint) public
