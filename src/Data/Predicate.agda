module Data.Predicate where

open import Prelude

private variable a : Set

record Predicate (a : Set) : Set where
  constructor Predicate:
  field getPredicate : a -> Bool

open Predicate

instance
  SemigroupPredicate : Semigroup (Predicate a)
  SemigroupPredicate ._<>_ (Predicate: p) (Predicate: q) =
    Predicate: λ a -> p a && q a

  MonoidPredicate : Monoid (Predicate a)
  MonoidPredicate .neutral = Predicate: (const True)

  FunctorPredicate : Contravariant Predicate
  FunctorPredicate .contramap f (Predicate: p) = Predicate: (p ∘ f)
