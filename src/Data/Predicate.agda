{-# OPTIONS --type-in-type #-}

module Data.Predicate where

open import Prelude

private variable a : Type

record Predicate (a : Type) : Type where
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
  Contravariant-Predicate .cmap f (Predicate: p) = Predicate: (p <<< f)
