{-# OPTIONS --type-in-type #-}

module Control.Thunk where

open import Control.Size

record Thunk (i : Size) (f : Size -> Set -> Set) (a : Set) : Set where
  coinductive
  field force : {j : Size< i} -> f j a

open Thunk public
