{-# OPTIONS --type-in-type #-}

module Data.Enum where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Colist

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    i : Size

-------------------------------------------------------------------------------
-- Enum
-------------------------------------------------------------------------------

record Enum (a : Set) : Set where
  field
    enumFromTo : a -> a -> List a
    enumFromThenTo : a -> a -> a -> List a
    enumFrom : a -> Colist a i
    enumFromThen : a -> a -> Colist a i

open Enum {{...}}
