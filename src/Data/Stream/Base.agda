{-# OPTIONS --type-in-type #-}

module Data.Stream.Base where

-- Stream X represents infinite lists of elements of X.

record Stream (X : Set) : Set where
  coinductive
  field
    head : X
    tail : Stream X

open Stream public

-- Stream is a functor.

open import Data.Functor public

instance
  Functor:Stream : Endofunctor Sets Stream
  Functor:Stream .map f xs .head = f (head xs)
  Functor:Stream .map f xs .tail = map f (tail xs)
