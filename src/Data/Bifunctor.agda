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
  first f = bimap f identity

  second : (B -> C) -> P A B -> P A C
  second g = bimap identity g

open Bifunctor {{...}} public

instance
  bifunctorConst : Bifunctor Const
  bifunctorConst .bimap f g (const: x) = const: (f x)

  bifunctorPair : Bifunctor _*_
  bifunctorPair .bimap f g = cross f g

  bifunctorEither : Bifunctor _+_
  bifunctorEither .bimap f g = plus f g
