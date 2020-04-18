{-# OPTIONS --type-in-type #-}

module Data.Semiring where

open import Data.Monoid
open import Data.Semigroup
open import Data.Type.Equality
open import Prim

private variable A B : Set

record Semiring (A : Set) : Set where
  field
    {{monoidSum}} : Monoid (Sum A)
    {{monoidProduct}} : Monoid (Product A)
    Nonzero : A -> Set

open Semiring {{...}} public
