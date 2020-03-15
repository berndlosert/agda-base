{-# OPTIONS --type-in-type #-}

module Data.Bifunctor where

open import Data.Pair
open import Data.Either
open import Data.Functor.Const
open import Prelude

private
  variable
    A B C D : Set

record Bifunctor (P : Set -> Set -> Set) : Set where
  field
    bimap : (A -> B) -> (C -> D) -> P A C -> P B D

  first : (A -> B) -> P A C -> P B C
  first f = bimap f id

  second : (B -> C) -> P A B -> P A C
  second g = bimap id g

open Bifunctor {{...}} public

instance
  Bifunctor:Const : Bifunctor Const
  Bifunctor:Const .bimap f g = \ where
    (Const: x) -> Const: (f x)

  Bifunctor:Pair : Bifunctor _*_
  Bifunctor:Pair .bimap f g = cross f g

  Bifunctor:Either : Bifunctor _+_
  Bifunctor:Either .bimap f g = plus f g
