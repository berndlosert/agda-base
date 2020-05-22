{-# OPTIONS --type-in-type #-}

module Data.Predicate where

open import Prelude

private variable A : Set

record Predicate (A : Set) : Set where
  constructor aPredicate
  field getPredicate : A -> Bool

open Predicate

instance
  semigroupPredicate : Semigroup (Predicate A)
  semigroupPredicate ._<>_ (aPredicate p) (aPredicate q) =
    aPredicate \ a -> p a && q a

  monoidPredicate : Monoid (Predicate A)
  monoidPredicate .neutral = aPredicate (const true)

  functorPredicate : Contravariant Predicate
  functorPredicate .contramap f (aPredicate p) = aPredicate (p <<< f)
