{-# OPTIONS --type-in-type #-}

module Data.Profunctor.Choice where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c : Set

-------------------------------------------------------------------------------
-- Choice
-------------------------------------------------------------------------------

record Choice (p : Set -> Set -> Set) : Set where
  field
    {{super}} : Profunctor p
    left : p a b -> p (a + c) (b + c)

  right : p a b -> p (c + a) (c + b)
  right = dimap (either Right Left) (either Right Left) <<< left

open Choice {{...}} public

instance
  Choice-Function : Choice Function
  Choice-Function .left ab (Left a) = Left (ab a)
  Choice-Function .left _ (Right c) = Right c
