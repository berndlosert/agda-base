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

record Thunk (i : Size) (f : Size -> Set) : Set where
  coinductive
  field force : {j : Size< i} -> f j

open Thunk public
