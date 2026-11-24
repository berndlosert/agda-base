module Control.Category where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Control.Semigroupoid using (Semigroupoid)
open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c : Type
    f : Type -> Type

-------------------------------------------------------------------------------
-- Category
-------------------------------------------------------------------------------

record Category {k : Type} (p : k -> k -> Type) : Type where
  field
    overlap {{Semigroupoid-super}} : Semigroupoid p
    id : {a : k} -> p a a

open Category {{...}} public

instance
  Category-Function : Category Function
  Category-Function .id x = x
