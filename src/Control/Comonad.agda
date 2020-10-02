{-# OPTIONS --type-in-type #-}

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
    extend : (w a -> b) -> w a -> w b
    extract : w a -> a

  duplicate : w a -> w (w a)
  duplicate = extend id

  infixl 1 _=>>_
  _=>>_ : w a -> (w a -> b) -> w b
  _=>>_ = flip extend

  infixl 1 _=>=_
  _=>=_ : (w a -> b) -> (w b -> c) -> (w a -> c)
  f =>= g = g <<< extend f

open Comonad {{...}} public
