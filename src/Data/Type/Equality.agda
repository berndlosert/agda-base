{-# OPTIONS --type-in-type #-}

module Data.Type.Equality where

open import Agda.Builtin.Equality public
  using (refl)
  renaming (_≡_ to _===_)

open import Agda.Builtin.TrustMe public
  renaming (primTrustMe to trustMe)
