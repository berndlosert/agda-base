{-# OPTIONS --type-in-type #-}

module Data.Fix where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Signature

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set

-------------------------------------------------------------------------------
-- Fix
-------------------------------------------------------------------------------

record Fix (sig : Signature) : Set where
  inductive
  pattern
  constructor toFix
  field unFix : Operation sig (Fix sig)

open Fix public

pattern sup op arg = toFix (operation op arg)

foldFix : {sig : Signature} -> Algebra sig a -> Fix sig -> a
foldFix alg (sup op arg) =
  let arg' x = foldFix alg (arg x)
  in alg (operation op arg')
