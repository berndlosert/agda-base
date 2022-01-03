module Control.Comonad where

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
-- Comonad
-------------------------------------------------------------------------------

record Comonad (w : Set -> Set) : Set where
  field
    {{super}} : Functor w
    extract : w a -> a
    extend : (w a -> b) -> w a -> w b

  duplicate : w a -> w (w a)
  duplicate = extend id

  infixl 1 _=>>_
  _=>>_ : w a -> (w a -> b) -> w b
  _=>>_ = flip extend

  infixl 1 _=>=_
  _=>=_ : (w a -> b) -> (w b -> c) -> (w a -> c)
  f =>= g = g <<< extend f

open Comonad {{...}} public

instance
  Comonad-Function : {{Monoid a}} -> Comonad (Function a)
  Comonad-Function .extract w = w mempty
  Comonad-Function .extend f w x = f \ y -> w (x <> y)
