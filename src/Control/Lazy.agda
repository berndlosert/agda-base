{-# OPTIONS --type-in-type #-}

module Control.Lazy where

open import Prelude

open import Agda.Builtin.Coinduction public
  renaming (
    ∞ to Lazy;
    ♯_ to delay;
    ♭ to force
  )

-- Lazy is a functor.
instance
  Functor:Lazy : Functor Lazy
  Functor:Lazy .map f x = delay (f (force x))
