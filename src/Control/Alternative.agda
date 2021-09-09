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
    a : Set

-------------------------------------------------------------------------------
-- Alternative
-------------------------------------------------------------------------------

record Alternative (f : Set -> Set) : Set where
  infixl 3 _<|>_
  field
    overlap {{Applicative-super}} : Applicative f
    _<|>_ : f a -> f a -> f a
    empty : f a

  guard : Bool -> f Unit
  guard true = pure tt
  guard false = empty

open Alternative {{...}} public

instance
  Alternative-Maybe : Alternative Maybe
  Alternative-Maybe .empty = nothing
  Alternative-Maybe ._<|>_ = \ where
    nothing r -> r
    l _ -> l

  Alternative-List : Alternative List
  Alternative-List .empty = neutral
  Alternative-List ._<|>_ = _<>_
