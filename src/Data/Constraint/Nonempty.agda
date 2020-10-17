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
    a : Set

-------------------------------------------------------------------------------
-- NonemptyConstraint
-------------------------------------------------------------------------------

record NonemptyConstraint (a : Set) : Set where
  field IsNonempty : a -> Set

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

Nonempty : (a : Set) {{_ : NonemptyConstraint a}} -> Set
Nonempty a = Constrained a IsNonempty
