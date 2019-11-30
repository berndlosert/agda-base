{-# OPTIONS --type-in-type #-}

module Data.Colist where

open import Control.Size
open import Control.Thunk

data Colist (i : Size) (X : Set) : Set where
  [] : Colist i X
  _::_ : X -> Thunk i Colist X -> Colist i X
