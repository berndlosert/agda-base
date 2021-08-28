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
    a b c d : Set

-------------------------------------------------------------------------------
-- Choice
-------------------------------------------------------------------------------

record Choice (p : Set -> Set -> Set) : Set where
  field
    overlap {{super}} : Profunctor p
    left : p a b -> p (Either a c) (Either b c)

  right : p a b -> p (Either c a) (Either c b)
  right = dimap (either Right Left) (either Right Left) <<< left

  infixr 2 _+++_
  _+++_ : {{Category p}} -> p a b -> p c d -> p (Either a c) (Either b d)
  f +++ g = left f >>> right g

  infixr 2 _|||_
  _|||_ : {{Category p}} -> p a c -> p b c -> p (Either a b) c
  f ||| g = map fromEither (f +++ g)

open Choice {{...}} public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Choice-Function : Choice Function
  Choice-Function .left ab (Left a) = Left (ab a)
  Choice-Function .left _ (Right c) = Right c
