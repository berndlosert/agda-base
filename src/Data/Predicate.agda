{-# OPTIONS --type-in-type #-}

module Data.Predicate where

open import Data.Functor.Contravariant
open import Prelude

private
  variable
    A : Set

record Predicate (A : Set) : Set where
  constructor Predicate:
  field
    get : A -> Bool

instance
  semigroupPredicate : Semigroup (Predicate A)
  semigroupPredicate ._<>_ (Predicate: p) (Predicate: q) =
    Predicate: (\ a -> p a && q a)

  monoidPredicate : Monoid (Predicate A)
  monoidPredicate .mempty = Predicate: (const true)

  functorPredicate : Contravariant Predicate
  functorPredicate .contramap f (Predicate: p) = Predicate: (f >>> p)
