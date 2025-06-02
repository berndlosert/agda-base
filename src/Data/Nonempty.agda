module Data.Nonempty where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Nonempty
-------------------------------------------------------------------------------

record Nonemptiness (a : Type) : Type where
  field
    Nonempty : Type
    overlap {{Semigroup-Nonempty}} : Semigroup Nonempty
    overlap {{Monoid-super}} : Monoid a
    nonempty : a -> Maybe Nonempty

open Nonemptiness {{...}} public
