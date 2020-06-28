{-# OPTIONS --type-in-type #-}

module Data.Predicate where

open import Prelude

private variable a : Set

record Predicate (a : Set) : Set where
  constructor Predicate:
  field getPredicate : a -> Bool

open Predicate

instance
  semigroupPredicate : Semigroup (Predicate a)
  semigroupPredicate ._<>_ (Predicate: p) (Predicate: q) =
    Predicate: λ a -> p a && q a

  monoidPredicate : Monoid (Predicate a)
  monoidPredicate .neutral = Predicate: (const True)

  functorPredicate : Contravariant Predicate
  functorPredicate .contramap f (Predicate: p) = Predicate: (p ∘ f)
