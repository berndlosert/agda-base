{-# OPTIONS --type-in-type #-}

module Control.Alternative where

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
-- Alternative
-------------------------------------------------------------------------------

record Alternative (f : Type -> Type) : Type where
  infixl 3 _<|>_
  field
    overlap {{Applicative-super}} : Applicative f
    _<|>_ : f a -> f a -> f a
    empty : f a

  guard : Bool -> f Unit
  guard True = pure unit
  guard False = empty

open Alternative {{...}} public

instance
  Alternative-Maybe : Alternative Maybe
  Alternative-Maybe .empty = Nothing
  Alternative-Maybe ._<|>_ = \ where
    Nothing r -> r
    l _ -> l

  Alternative-List : Alternative List
  Alternative-List .empty = neutral
  Alternative-List ._<|>_ = _<>_
