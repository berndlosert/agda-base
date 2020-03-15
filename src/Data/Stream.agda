{-# OPTIONS --type-in-type #-}

module Data.Stream where

open import Prelude

private
  variable
    A : Set

-- Stream A represents infinite lists of elements of A.
record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A

open Stream public

-- Stream forms a functor.
instance
  Functor:Stream : Functor Stream
  Functor:Stream .map f as .head = f (head as)
  Functor:Stream .map f as .tail = map f (tail as)

-- Stream forms an applicative.
instance
  Applicative:Stream : Applicative Stream
  Applicative:Stream .pure a .head = a
  Applicative:Stream .pure a .tail = pure a
  Applicative:Stream ._<*>_ fs as .head = head fs (head as)
  Applicative:Stream ._<*>_ fs as .tail = tail fs <*> tail as

-- Stream forms a comonad.
open import Control.Comonad

instance
  Comonad:Stream : Comonad Stream
  Comonad:Stream .extend f as = pure (f as)
  Comonad:Stream .extract as = head as

-- iterate f a creates the stream [ a # f a # f (f a) # ... ].
iterate : forall {A} -> (A -> A) -> A -> Stream A
iterate f a .head = a
iterate f a .tail = iterate f (f a)

-- repeat a is the infinite list [ a # a # a # ... ].
repeat : forall {A} -> A -> Stream A
repeat a .head = a
repeat a .tail = repeat a

-- Preprend a list to a stream.
prepend : forall {A} -> List A -> Stream A -> Stream A
prepend [] ys = ys
prepend (a :: as) ys .head = a
prepend (a :: as) ys .tail = prepend as ys

-- Take the first n elements of a stream.
take : forall {A} -> Nat -> Stream A -> List A
take 0 _ = []
take (suc n) as = head as :: take n (tail as)
