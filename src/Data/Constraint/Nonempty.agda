{-# OPTIONS --type-in-type #-}

module Data.Constraint.Nonempty where

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
    a : Type

-------------------------------------------------------------------------------
-- NonemptyConstraint
-------------------------------------------------------------------------------

record NonemptyConstraint (a : Type) : Type where
  field IsNonempty : a -> Type

open NonemptyConstraint {{...}} public

instance
  NonemptyConstraint-List : NonemptyConstraint (List a)
  NonemptyConstraint-List .IsNonempty [] = Void
  NonemptyConstraint-List .IsNonempty _ = Unit

  NonemptyConstraint-String : NonemptyConstraint String
  NonemptyConstraint-String .IsNonempty "" = Void
  NonemptyConstraint-String .IsNonempty _ = Unit

-------------------------------------------------------------------------------
-- Nonempty
-------------------------------------------------------------------------------

Nonempty : (a : Type) {{_ : NonemptyConstraint a}} -> Type
Nonempty a = Constrained a IsNonempty
