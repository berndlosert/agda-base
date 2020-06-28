{-# OPTIONS --type-in-type #-}

module Control.Comonad where

open import Prelude

private variable a b c : Set

record Comonad (w : Set -> Set) : Set where
  infixl 1 _=>>_ _=>=_
  field
    {{functor}} : Functor w
    extend : (w a -> b) -> w a -> w b
    extract : w a -> a

  duplicate : w a -> w (w a)
  duplicate = extend id

  _=>>_ : w a -> (w a -> b) -> w b
  _=>>_ = flip extend

  _=>=_ : (w a -> b) -> (w b -> c) -> (w a -> c)
  f =>= g = g ∘ extend f

open Comonad {{...}} public
