{-# OPTIONS --type-in-type #-}

module Control.Monad.Random.Class where

open import Prelude

private variable a : Set

abstract
  Range : Set -> Set
  Range a = a * a

  getRange : Range a -> a * a
  getRange = id

  mkRange : {{_ : Ord a}} (l u : a) {{_ : Assert $ l < u}} -> Range a
  mkRange l u = (l , u)

record MonadRandom (m : Set -> Set) : Set where
  field
    getRandom : m a
    getRandoms : m (List a)
    getRandomR : Range a -> m a
    getRandomRs : Range a -> m (List a)

open MonadRandom {{...}} public
