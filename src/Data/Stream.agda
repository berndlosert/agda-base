{-# OPTIONS --type-in-type #-}

module Data.Stream where

-- Stream X represents infinite lists of elements of X.
record Stream (X : Set) : Set where
  coinductive
  field
    head : X
    tail : Stream X

open Stream

open import Control.Category
open import Data.Functor

instance
  -- Stream is a functor. 
  Functor:Stream : Endofunctor Sets Stream
  Functor:Stream .map f xs .head = f (head xs)
  Functor:Stream .map f xs .tail = map f (tail xs)

private variable X : Set

-- iterate f x creates the stream [ x # f x # f (f x) # ... ].
iterate : (X -> X) -> X -> Stream X 
iterate f x .head = x
iterate f x .tail = iterate f (f x)

-- repeat x is the infinite list [ x # x # x # ... ].
repeat : X -> Stream X
repeat x .head = x
repeat x .tail = repeat x

open import Data.List using (List; _::_; [])

-- Preprend a list to a stream.
prepend : List X -> Stream X -> Stream X
prepend [] ys = ys
prepend (x :: xs) ys .head = x 
prepend (x :: xs) ys .tail = prepend xs ys

open import Data.Nat

-- Take the first n elements of a stream.
take : Nat -> Stream X -> List X
take 0 _ = []
take (suc n) xs = head xs :: take n (tail xs)
