{-# OPTIONS --type-in-type #-}

module Data.FingerTree.Measured where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Measured
-------------------------------------------------------------------------------

record Measured (v a : Set) : Set where
  field
    overlap {{Monoid-v}} : Monoid v
    measure : a -> v

open Measured {{...}} public
