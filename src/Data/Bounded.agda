{-# OPTIONS --type-in-type #-}

module Data.Bounded where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Bounded
-------------------------------------------------------------------------------

record Bounded (a : Type) : Type where
  field
    overlap {{Ord-super}} : Ord a
    minBound : a
    maxBound : a

open Bounded {{...}} public

instance
  Bounded-Char : Bounded Char
  Bounded-Char .minBound = minChar
  Bounded-Char .maxBound = maxChar

  Bounded-Float : Bounded Float
  Bounded-Float .minBound = Infinity
  Bounded-Float .maxBound = -Infinity
