{-# OPTIONS --type-in-type #-}

module Data.Fix where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Container

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set

-------------------------------------------------------------------------------
-- Fix
-------------------------------------------------------------------------------

record Fix (c : Container) : Set where
  inductive
  pattern
  constructor toFix
  field unFix : Extension c (Fix c)

open Fix public

foldFix : {c : Container} -> (Extension c a -> a) -> Fix c -> a
foldFix alg (toFix (extension s p)) = alg (extension s \ x -> foldFix alg (p x))
