{-# OPTIONS --type-in-type #-}

module Data.Thunk where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Functor.Coyoneda

-------------------------------------------------------------------------------
-- Thunk
-------------------------------------------------------------------------------

record Thunk (f : Size -> Set) (i : Size) : Set where
  coinductive
  field force : {j : Size< i} -> f j

open Thunk public
