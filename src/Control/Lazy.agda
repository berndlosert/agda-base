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
  functorLazy : Functor Lazy
  functorLazy .map f x = delay (f (force x))
