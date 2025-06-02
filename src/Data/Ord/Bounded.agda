module Data.Ord.Bounded where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Char as Char using ()
open import Data.Float as Float using ()

-------------------------------------------------------------------------------
-- Bounded
-------------------------------------------------------------------------------

record Bounded (a : Type) : Type where
  field
    overlap {{Ord-super}} : Ord a
    hasMinBound : Bool
    hasMaxBound : Bool
    minBound : {{Assert hasMinBound}} -> a
    maxBound : {{Assert hasMaxBound}} -> a

open Bounded {{...}} public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Bounded-Unit : Bounded Unit
  Bounded-Unit .hasMinBound = true
  Bounded-Unit .hasMaxBound = true
  Bounded-Unit .minBound = tt
  Bounded-Unit .maxBound = tt

  Bounded-Bool : Bounded Bool
  Bounded-Bool .hasMinBound = true
  Bounded-Bool .hasMaxBound = true
  Bounded-Bool .minBound = false
  Bounded-Bool .maxBound = true

  Bounded-Nat : Bounded Nat
  Bounded-Nat .hasMinBound = true
  Bounded-Nat .hasMaxBound = false
  Bounded-Nat .minBound = 0

  Bounded-Float : Bounded Float
  Bounded-Float .hasMinBound = true
  Bounded-Float .hasMaxBound = true
  Bounded-Float .minBound = Float.infinity
  Bounded-Float .maxBound = (- Float.infinity)

  Bounded-Char : Bounded Char
  Bounded-Char .hasMinBound = true
  Bounded-Char .hasMaxBound = true
  Bounded-Char .minBound = Char.minChar
  Bounded-Char .maxBound = Char.maxChar
