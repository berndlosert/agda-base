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
  field Positive : a -> Set

open PositiveConstraint {{...}} public

instance
  PositiveConstraint-Nat : PositiveConstraint Nat
  PositiveConstraint-Nat .Positive 0 = Void
  PositiveConstraint-Nat .Positive _ = Unit

  PositiveConstraint-Int : PositiveConstraint Int
  PositiveConstraint-Int .Positive (Pos 0) = Void
  PositiveConstraint-Int .Positive (NegSuc _) = Void
  PositiveConstraint-Int .Positive _ = Unit

  PositiveConstraint-Float : PositiveConstraint Float
  PositiveConstraint-Float .Positive x = Assert (x > 0.0)
