{-# OPTIONS --type-in-type #-}

module Data.Constraint.Constrained where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Constrained
-------------------------------------------------------------------------------

record Constrained (a : Type) (p : a -> Type) : Type where
  constructor Constrained:
  field
    unconstrained : a
    {{constraintProof}} : p unconstrained

open Constrained public
