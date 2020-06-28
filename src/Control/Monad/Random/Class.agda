{-# OPTIONS --type-in-type #-}

module Control.Monad.Random.Class where

open import Prelude

private variable A : Set

abstract
  Range : Set -> Set
  Range A = A * A

  getRange : Range A -> A * A
  getRange = id

  mkRange : {{_ : Ord A}} (a a' : A) {_ : (a < a') === True} -> Range A
  mkRange a a' = (a , a')

record MonadRandom (M : Set -> Set) : Set where
  field
    getRandom : M A
    getRandoms : M (List A)
    getRandomR : Range A -> M A
    getRandomRs : Range A -> M (List A)

open MonadRandom {{...}} public
