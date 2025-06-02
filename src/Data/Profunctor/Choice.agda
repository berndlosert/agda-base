module Data.Profunctor.Choice where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Profunctor

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
    mapLeft : p a b -> p (Either a c) (Either b c)

  mapRight : p a b -> p (Either c a) (Either c b)
  mapRight = dimap mirror mirror <<< mapLeft

  infixr 2 _+++_
  _+++_ : {{Category p}} -> p a b -> p c d -> p (Either a c) (Either b d)
  f +++ g = mapLeft f >>> mapRight g

  infixr 2 _|||_
  _|||_ : {{Category p}} -> p a c -> p b c -> p (Either a b) c
  f ||| g = uneither <$> (f +++ g)

open Choice {{...}} public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Choice-Function : Choice Function
  Choice-Function .mapLeft ab (left a) = left (ab a)
  Choice-Function .mapLeft _ (right c) = right c
