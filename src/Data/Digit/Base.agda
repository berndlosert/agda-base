{-# OPTIONS --type-in-type #-}

module Data.Digit.Base where

-- Digit is used to represent the decimal digits.

data Digit : Set where
  0d 1d 2d 3d 4d 5d 6d 7d 8d 9d : Digit
