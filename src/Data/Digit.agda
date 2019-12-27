{-# OPTIONS --type-in-type #-}

module Data.Digit where

open import Data.Digit.Base public
  hiding (module Digit)

module Digit where
  open import Data.Digit.Api public
    hiding (
      Eq:Digit; 
      Ord:Digit
    )

open import Data.Digit.Api public
  using (
    Eq:Digit; 
    Ord:Digit
  )
