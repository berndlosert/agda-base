module Data.Bounds where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Char as Char using ()
open import Data.Float as Float using ()

-------------------------------------------------------------------------------
-- Bounds
-------------------------------------------------------------------------------

record Bounds (a : Set) : Set where
  field
    overlap {{Ord-super}} : Ord a
    minBound : Maybe a
    maxBound : Maybe a

open Bounds {{...}} public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Bounds-Unit : Bounds Unit
  Bounds-Unit .minBound = just tt
  Bounds-Unit .maxBound = just tt

  Bounds-Bool : Bounds Bool
  Bounds-Bool .minBound = just false
  Bounds-Bool .maxBound = just true

  Bounds-Nat : Bounds Nat
  Bounds-Nat .minBound = just 0
  Bounds-Nat .maxBound = nothing

  Bounds-Int : Bounds Int
  Bounds-Int .minBound = nothing
  Bounds-Int .maxBound = nothing

  Bounds-Float : Bounds Float
  Bounds-Float .minBound = just Float.infinity
  Bounds-Float .maxBound = just (- Float.infinity)

  Bounds-Char : Bounds Char
  Bounds-Char .minBound = just Char.minChar
  Bounds-Char .maxBound = just Char.maxChar
