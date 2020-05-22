{-# OPTIONS --type-in-type #-}

module Control.Comonad where

open import Prelude

private variable A B C : Set

record Comonad (W : Set -> Set) : Set where
  infixl 1 _=>>_ _=>=_
  field
    {{functor}} : Functor W
    extend : (W A -> B) -> W A -> W B
    extract : W A -> A

  duplicate : W A -> W (W A)
  duplicate = extend id

  _=>>_ : W A -> (W A -> B) -> W B
  _=>>_ = flip extend

  _=>=_ : (W A -> B) -> (W B -> C) -> (W A -> C)
  f =>= g = g <<< extend f

open Comonad {{...}} public
