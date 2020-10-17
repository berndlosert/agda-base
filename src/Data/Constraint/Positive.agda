{-# OPTIONS --type-in-type #-}

module Data.Constraint.Positive where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open import Data.Constraint.Constrained public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set

-------------------------------------------------------------------------------
-- PositiveConstraint
-------------------------------------------------------------------------------

record PositiveConstraint (a : Set) : Set where
  field IsPositive : a -> Set

open PositiveConstraint {{...}} public

instance
  PositiveConstraint-Nat : PositiveConstraint Nat
  PositiveConstraint-Nat .IsPositive 0 = Void
  PositiveConstraint-Nat .IsPositive _ = Unit

  PositiveConstraint-Int : PositiveConstraint Int
  PositiveConstraint-Int .IsPositive (Pos 0) = Void
  PositiveConstraint-Int .IsPositive (NegSuc _) = Void
  PositiveConstraint-Int .IsPositive _ = Unit

  PositiveConstraint-Float : PositiveConstraint Float
  PositiveConstraint-Float .IsPositive x = Assert (x > 0.0)

-------------------------------------------------------------------------------
-- Positive
-------------------------------------------------------------------------------

Positive : (a : Set) {{_ : PositiveConstraint a}} -> Set
Positive a = Constrained a IsPositive
