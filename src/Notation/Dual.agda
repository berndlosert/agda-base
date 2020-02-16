{-# OPTIONS --type-in-type #-}

module Notation.Dual where

-- We use this to define the dual or opposite versions of certain
-- mathatematical structures.

record Dual (S : Set) : Set where
  constructor Dual:
  field
     Op : S -> S

open Dual {{...}} public
