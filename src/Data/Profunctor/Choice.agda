module Data.Profunctor.Choice where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude as Prelude

open import Control.Category
open import Data.Profunctor

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
    mapLeft : p a b -> p (Either a c) (Either b c)

  mapRight : p a b -> p (Either c a) (Either c b)
  mapRight = dimap mirror mirror <<< mapLeft

  infixr 2 _+++_
  _+++_ : {{Category p}} -> p a b -> p c d -> p (Either a c) (Either b d)
  f +++ g = mapLeft f andThen mapRight g

  infixr 2 _|||_
  _|||_ : {{Category p}} -> p a c -> p b c -> p (Either a b) c
  f ||| g = map fromEither (f +++ g)

open Choice {{...}} public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Choice-Function : Choice Function
  Choice-Function .mapLeft ab (left a) = left (ab a)
  Choice-Function .mapLeft _ (right c) = right c
