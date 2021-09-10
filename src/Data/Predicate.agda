{-# OPTIONS --type-in-type #-}

module Data.Predicate where

open import Prelude

private variable a : Set

record Predicate (a : Set) : Set where
  constructor toPredicate
  field getPredicate : a -> Bool

open Predicate

instance
  Semigroup-Predicate : Semigroup (Predicate a)
  Semigroup-Predicate ._<>_ (toPredicate p) (toPredicate q) =
    toPredicate \ a -> p a && q a

  Monoid-Predicate : Monoid (Predicate a)
  Monoid-Predicate .mempty = toPredicate (const true)

  Contravariant-Predicate : Contravariant Predicate
  Contravariant-Predicate .cmap f (toPredicate p) = toPredicate (p <<< f)
