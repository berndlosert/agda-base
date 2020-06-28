{-# OPTIONS --type-in-type #-}

module Control.Size where

open import Agda.Builtin.Size public
  renaming (
    ↑_ to szSuc;
    _⊔ˢ_ to szmax;
    ∞ to infty
  )
