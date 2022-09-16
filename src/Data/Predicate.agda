module Data.Predicate where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Functor.Contravariant

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set

-------------------------------------------------------------------------------
-- Predicate
-------------------------------------------------------------------------------

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
