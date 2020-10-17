{-# OPTIONS --type-in-type #-}

module Data.Constraint.Constrained where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Constrained
-------------------------------------------------------------------------------

record Constrained (a : Set) (p : a -> Set) : Set where
  constructor Constrained:
  field
    unconstrained : a
    {{constraintProof}} : p unconstrained

open Constrained public
