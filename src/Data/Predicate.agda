{-# OPTIONS --type-in-type #-}

module Data.Predicate where

open import Prelude

private variable A : Set

record Predicate (A : Set) : Set where
  constructor toPredicate
  field fromPredicate : A -> Bool

open Predicate

instance
  semigroupPredicate : Semigroup (Predicate A)
  semigroupPredicate ._<>_ (Predicate: p) (Predicate: q) =
    Predicate: (\ a -> p a && q a)

  monoidPredicate : Monoid (Predicate A)
  monoidPredicate .empty = Predicate: (const true)

  functorPredicate : Contravariant Predicate
  functorPredicate .contramap f (Predicate: p) = Predicate: (f >>> p)
