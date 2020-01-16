{-# OPTIONS --type-in-type #-}

module Data.Monoid where

-- A semigroup is a monoid when its binary operation has an identity.

open import Data.Semigroup public

record Monoid (X : Set) : Set where
  constructor Monoid:
  field
    overlap {{Semigroup:Monoid}} : Semigroup X
    mempty : X

open Monoid {{...}} public
