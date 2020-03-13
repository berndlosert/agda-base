{-# OPTIONS --type-in-type #-}

module Data.Predicate where

open import Data.Functor.Contravariant
open import Prelude

record Predicate (X : Set) : Set where
  constructor Predicate:
  field
    get : X -> Bool

instance
  Semigroup:Predicate : forall {X} -> Semigroup (Predicate X)
  Semigroup:Predicate ._<>_ (Predicate: p) (Predicate: q) =
    Predicate: (\ x -> p x && q x)

  Monoid:Predicate : forall {X} -> Monoid (Predicate X)
  Monoid:Predicate .mempty = Predicate: (const true)

  Functor:Predicate : Contravariant Predicate
  Functor:Predicate .map f (Predicate: p) = Predicate: (f >>> p)
