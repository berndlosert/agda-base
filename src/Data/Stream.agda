{-# OPTIONS --type-in-type #-}

module Data.Stream where

open import Prelude

private variable A : Set

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A

open Stream public

-- Stream forms a functor.
instance
  functorStream : Functor Stream
  functorStream .map f as .head = f (head as)
  functorStream .map f as .tail = map f (tail as)

-- Stream forms an applicative.
instance
  applicativeStream : Applicative Stream
  applicativeStream .pure a .head = a
  applicativeStream .pure a .tail = pure a
  applicativeStream ._<*>_ fs as .head = head fs (head as)
  applicativeStream ._<*>_ fs as .tail = tail fs <*> tail as

-- Stream forms a comonad.
open import Control.Comonad

instance
  comonadStream : Comonad Stream
  comonadStream .extend f as = pure (f as)
  comonadStream .extract as = head as

iterate : (A -> A) -> A -> Stream A
iterate f a .head = a
iterate f a .tail = iterate f (f a)

repeat : A -> Stream A
repeat a .head = a
repeat a .tail = repeat a

prepend : List A -> Stream A -> Stream A
prepend [] ys = ys
prepend (a :: as) ys .head = a
prepend (a :: as) ys .tail = prepend as ys

take : Nat -> Stream A -> List A
take 0 _ = []
take (suc n) as = head as :: take n (tail as)
