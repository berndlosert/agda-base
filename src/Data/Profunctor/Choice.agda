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
    choicel : p a b -> p (Either a c) (Either b c)

  choicer : p a b -> p (Either c a) (Either c b)
  choicer = dimap (either Right Left) (either Right Left) <<< choicel

  infixr 2 _+++_
  _+++_ : {{Category p}} -> p a b -> p c d -> p (Either a c) (Either b d)
  f +++ g = choicel f >>> choicer g

  infixr 2 _|||_
  _|||_ : {{Category p}} -> p a c -> p b c -> p (Either a b) c
  f ||| g = map fromEither (f +++ g)

open Choice {{...}} public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Choice-Function : Choice Function
  Choice-Function .choicel ab (Left a) = Left (ab a)
  Choice-Function .choicel _ (Right c) = Right c
