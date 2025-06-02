module Data.Semigroup.FromMaybe where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Type

-------------------------------------------------------------------------------
-- FromMaybe
-------------------------------------------------------------------------------

record FromMaybe (a : Type) : Type where
  constructor asFromMaybe
  field appFromMaybe : Maybe a -> a

open FromMaybe public

instance
  Semigroup-FromMaybe : Semigroup (FromMaybe a)
  Semigroup-FromMaybe ._<>_ g f = 
    asFromMaybe (appFromMaybe g <<< just <<< appFromMaybe f)
