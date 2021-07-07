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
    a b c d : Type

-------------------------------------------------------------------------------
-- Choice
-------------------------------------------------------------------------------

record Choice (p : Type -> Type -> Type) : Type where
  field
    overlap {{super}} : Profunctor p
    left : p a b -> p (a + c) (b + c)

  right : p a b -> p (c + a) (c + b)
  right = dimap (either Right Left) (either Right Left) <<< left

  infixr 2 _+++_
  _+++_ : {{_ : Category p}} -> p a b -> p c d -> p (a + c) (b + d)
  f +++ g = left f >>> right g

  infixr 2 _|||_
  _|||_ : {{_ : Category p}} -> p a c -> p b c -> p (a + b) c
  f ||| g = map fromEither (f +++ g)

open Choice {{...}} public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Choice-Function : Choice Function
  Choice-Function .left ab (Left a) = Left (ab a)
  Choice-Function .left _ (Right c) = Right c
