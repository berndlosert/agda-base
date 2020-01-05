{-# OPTIONS --type-in-type #-}

module Data.Stream.Base where

-- Stream X represents infinite lists of elements of X.

record Stream (X : Set) : Set where
  coinductive
  field
    head : X
    tail : Stream X

open Stream public
