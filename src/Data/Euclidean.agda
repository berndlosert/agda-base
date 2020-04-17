{-# OPTIONS --type-in-type #-}

module Data.Euclidean where

open import Data.Semiring
open import Prim

record Euclidean (A : Set) : Set where
  field
    {{super}} : Semiring A
    degree : A -> Nat
    quot : (a b : A) {_ : Nonzero b} -> A
    mod : (a b : A) {_ : Nonzero b} -> A

open Euclidean {{...}} public
