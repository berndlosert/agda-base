{-# OPTIONS --type-in-type #-}

module Data.Bifunctor where

open import Prelude

open import Data.Functor.Const

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
  bifunctorConst : Bifunctor Const
  bifunctorConst .bimap f g = toConst <<< f <<< fromConst

  bifunctorPair : Bifunctor Pair
  bifunctorPair .bimap f g = cross f g

  bifunctorEither : Bifunctor Either
  bifunctorEither .bimap f g = plus f g
