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
  Semigroup:Predicate : Semigroup (Predicate A)
  Semigroup:Predicate ._<>_ (Predicate: p) (Predicate: q) =
    Predicate: (\ a -> p a && q a)

  Monoid:Predicate : Monoid (Predicate A)
  Monoid:Predicate .mempty = Predicate: (const true)

  Functor:Predicate : Contravariant Predicate
  Functor:Predicate .contramap f (Predicate: p) = Predicate: (f >>> p)
