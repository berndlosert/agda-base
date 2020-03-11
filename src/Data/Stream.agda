{-# OPTIONS --type-in-type #-}

module Data.Stream where

open import Prelude

-- Stream X represents infinite lists of elements of X.
record Stream (X : Set) : Set where
  coinductive
  field
    head : X
    tail : Stream X

open Stream public

-- Stream forms a functor.
instance
  Functor:Stream : Functor Stream
  Functor:Stream .map f xs .head = f (head xs)
  Functor:Stream .map f xs .tail = map f (tail xs)

-- Stream forms an applicative.
instance
  Applicative:Stream : Applicative Stream
  Applicative:Stream .pure x .head = x
  Applicative:Stream .pure x .tail = pure x
  Applicative:Stream ._<*>_ fs xs .head = head fs (head xs)
  Applicative:Stream ._<*>_ fs xs .tail = tail fs <*> tail xs

-- Stream forms a comonad.
open import Control.Comonad

instance
  Comonad:Stream : Comonad Sets Stream
  Comonad:Stream .coextend f xs = pure (f xs)
  Comonad:Stream .extract xs = head xs

-- iterate f x creates the stream [ x # f x # f (f x) # ... ].
iterate : forall {X} -> (X -> X) -> X -> Stream X
iterate f x .head = x
iterate f x .tail = iterate f (f x)

-- repeat x is the infinite list [ x # x # x # ... ].
repeat : forall {X} -> X -> Stream X
repeat x .head = x
repeat x .tail = repeat x

-- Preprend a list to a stream.
prepend : forall {X} -> List X -> Stream X -> Stream X
prepend [] ys = ys
prepend (x :: xs) ys .head = x
prepend (x :: xs) ys .tail = prepend xs ys

-- Take the first n elements of a stream.
take : forall {X} -> Nat -> Stream X -> List X
take 0 _ = []
take (suc n) xs = head xs :: take n (tail xs)
