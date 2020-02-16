{-# OPTIONS --type-in-type #-}

module Data.Semigroup where

-- A semigroup is a type equipped with an associative binary operation.

record Semigroup (X : Set) : Set where
  constructor Semigroup:
  infixr 6 _<>_
  field _<>_ : X -> X -> X

open Semigroup {{...}} public

-- Every semigroup instance has an opposite version.

open import Notation.Dual public

instance
  Dual:Semigroup : forall {X} -> Dual (Semigroup X)
  Dual:Semigroup .Op (Semigroup: _<>_) = Semigroup: \ x y -> y <> x
