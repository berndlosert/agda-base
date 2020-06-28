{-# OPTIONS --type-in-type #-}

module Data.Colist where

open import Control.Size
open import Control.Thunk

data Colist (i : Size) (a : Set) : Set where
  [] : Colist i a
  _::_ : a -> Thunk i Colist a -> Colist i a
