module Data.Profunctor where

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
-- Profunctor
-------------------------------------------------------------------------------

record Profunctor (p : Set -> Set -> Set) : Set where
  field
    overlap {{Functor-super}} : Functor (p a)
    lcmap : (b -> a) -> p a c -> p b c

  dimap : (a -> b) -> (c -> d) -> p b c -> p a d
  dimap f g = lcmap f <<< map g

  arr : {{Category p}} -> (a -> b) -> p a b
  arr f = map f id

open Profunctor {{...}} public

instance
  Profunctor-Function : Profunctor Function
  Profunctor-Function .lcmap = _>>>_