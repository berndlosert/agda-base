{-# OPTIONS --type-in-type #-}

module Data.Stream where

open import Data.Stream.Base public
  hiding (module Stream)

module Stream where

  -- Stream is a functor.
  
  open import Control.Category
  open import Data.Functor
  
  instance
    Functor:Stream : Endofunctor Sets Stream
    Functor:Stream .map f xs .head = f (head xs)
    Functor:Stream .map f xs .tail = map f (tail xs)
  
  -- iterate f x creates the stream [ x # f x # f (f x) # ... ].
  
  iterate : forall {X} -> (X -> X) -> X -> Stream X
  iterate f x .head = x
  iterate f x .tail = iterate f (f x)
  
  -- repeat x is the infinite list [ x # x # x # ... ].
  
  repeat : forall {X} -> X -> Stream X
  repeat x .head = x
  repeat x .tail = repeat x
  
  -- Preprend a list to a stream.
  
  open import Data.List using (List; _::_; [])
  
  prepend : forall {X} -> List X -> Stream X -> Stream X
  prepend [] ys = ys
  prepend (x :: xs) ys .head = x
  prepend (x :: xs) ys .tail = prepend xs ys
  
  -- Take the first n elements of a stream.
  
  open import Data.Nat
  
  take : forall {X} -> Nat -> Stream X -> List X
  take 0 _ = []
  take (suc n) xs = head xs :: take n (tail xs)

open Stream
  using (Functor:Stream)
