module Data.Bifunctor where

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
-- Bifunctor
-------------------------------------------------------------------------------

record Bifunctor (p : Set -> Set -> Set) : Set where
  field
    overlap {{Functor-super}} : Functor (p a)
    lmap : (a -> b) -> p a c -> p b c

  bimap : (a -> b) -> (c -> d) -> p a c -> p b d
  bimap f g = lmap f <<< map g

open Bifunctor {{...}} public

instance
  Bifunctor-Either : Bifunctor Either
  Bifunctor-Either .lmap f = either (left <<< f) right

  Bifunctor-Pair : Bifunctor Pair
  Bifunctor-Pair .lmap f (x , y) = (f x , y)