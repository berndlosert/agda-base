{-# OPTIONS --type-in-type #-}

module Data.Bounded where

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
    minBound : a
    maxBound : a

open Bounded {{...}} public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Bounded-Char : Bounded Char
  Bounded-Char .minBound = Char.minChar
  Bounded-Char .maxBound = Char.maxChar

  Bounded-Float : Bounded Float
  Bounded-Float .minBound = Float.Infinity
  Bounded-Float .maxBound = Float.-Infinity
