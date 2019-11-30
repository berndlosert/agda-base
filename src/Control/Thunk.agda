{-# OPTIONS --type-in-type #-}

module Control.Thunk where

open import Control.Size

record Thunk (i : Size) (F : Size → Set → Set) (X : Set) : Set where
  coinductive
  field
    force : {j : Size< i} → F j X

open Thunk public
