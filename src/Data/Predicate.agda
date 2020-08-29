module Data.Predicate where

open import Prelude

private variable a : Set

record Predicate (a : Set) : Set where
  constructor Predicate:
  field getPredicate : a -> Bool

open Predicate

instance
  Semigroup-Predicate : Semigroup (Predicate a)
  Semigroup-Predicate ._<>_ (Predicate: p) (Predicate: q) =
    Predicate: \ a -> p a && q a

  Monoid-Predicate : Monoid (Predicate a)
  Monoid-Predicate .neutral = Predicate: (const True)

  Contravariant-Predicate : Contravariant Predicate
  Contravariant-Predicate .contramap f (Predicate: p) = Predicate: (p ∘ f)
