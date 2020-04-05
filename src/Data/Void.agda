{-# OPTIONS --type-in-type #-}

module Data.Void where

private variable A : Set

data Void : Set where

absurd : Void -> A
absurd ()
