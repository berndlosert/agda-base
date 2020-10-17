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
  field Nonempty : a -> Set

open NonemptyConstraint {{...}} public

instance
  NonemptyConstraint-List : NonemptyConstraint (List a)
  NonemptyConstraint-List .Nonempty [] = Void
  NonemptyConstraint-List .Nonempty _ = Unit

  NonemptyConstraint-String : NonemptyConstraint String
  NonemptyConstraint-String .Nonempty "" = Void
  NonemptyConstraint-String .Nonempty _ = Unit
