{-# OPTIONS --type-in-type #-}

module Data.Predicate where

open import Prelude

private variable a : Set

record Predicate (a : Set) : Set where
  constructor aPredicate
  field getPredicate : a -> Bool

open Predicate

instance
  Semigroup-Predicate : Semigroup (Predicate a)
  Semigroup-Predicate ._<>_ (aPredicate p) (aPredicate q) =
    aPredicate \ a -> p a && q a

  Monoid-Predicate : Monoid (Predicate a)
  Monoid-Predicate .mempty = aPredicate (const true)

  Contravariant-Predicate : Contravariant Predicate
  Contravariant-Predicate .cmap f (aPredicate p) = aPredicate (p <<< f)
