{-# OPTIONS --type-in-type --sized-types #-}

module Data.Size where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Size
-------------------------------------------------------------------------------

open import Agda.Builtin.Size public
  using (SizeUniv)
  using (Size)
  using (Size<_)
  renaming (↑_ to SizeSuc)
  renaming (∞ to SizeInf)
  renaming (_⊔ˢ_ to SizeMax)

-------------------------------------------------------------------------------
-- Thunk
-------------------------------------------------------------------------------

record Thunk (i : Size) (f : Size -> Set) : Set where
  coinductive
  field force : {j : Size< i} -> f j

open Thunk public
