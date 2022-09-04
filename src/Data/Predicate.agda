module Data.Predicate where

open import Prelude

private variable a : Set

record Predicate (a : Set) : Set where
  constructor asPredicate
  field getPredicate : a -> Bool

open Predicate public

instance
  Semigroup-Predicate : Semigroup (Predicate a)
  Semigroup-Predicate ._<>_ (asPredicate p) (asPredicate q) =
    asPredicate \ a -> p a && q a

  Monoid-Predicate : Monoid (Predicate a)
  Monoid-Predicate .mempty = asPredicate (const true)

  Contravariant-Predicate : Contravariant Predicate
  Contravariant-Predicate .cmap f (asPredicate p) = asPredicate (p <<< f)
