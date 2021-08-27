{-# OPTIONS --type-in-type --guardedness #-}

module Data.Stream where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Comonad
open import Data.List as List using ()

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Type

-------------------------------------------------------------------------------
-- Stream
-------------------------------------------------------------------------------

record Stream (a : Type) : Type where
  coinductive
  field
    head : a
    tail : Stream a

open Stream public

instance
  Functor-Stream : Functor Stream
  Functor-Stream .map f as .head = f (head as)
  Functor-Stream .map f as .tail = map f (tail as)

  Applicative-Stream : Applicative Stream
  Applicative-Stream .pure a .head = a
  Applicative-Stream .pure a .tail = pure a
  Applicative-Stream ._<*>_ fs as .head = head fs (head as)
  Applicative-Stream ._<*>_ fs as .tail = tail fs <*> tail as

  Comonad-Stream : Comonad Stream
  Comonad-Stream .extend f as = pure (f as)
  Comonad-Stream .extract as = head as

iterate : (a -> a) -> a -> Stream a
iterate f a .head = a
iterate f a .tail = iterate f (f a)

unfold : (b -> Pair a b) -> b -> Stream a
unfold f b = let (a , b') = f b in \ where
  .head -> a
  .tail -> unfold f b'

repeat : a -> Stream a
repeat a .head = a
repeat a .tail = repeat a

prepend : List a -> Stream a -> Stream a
prepend [] ys = ys
prepend (a :: as) ys .head = a
prepend (a :: as) ys .tail = prepend as ys

take : Nat -> Stream a -> List a
take 0 _ = []
take (Suc n) as = head as :: take n (tail as)

at : Nat -> Stream a -> a
at 0 as = head as
at (Suc n) as = at n (tail as)

cycle : (as : List a) -> {{Validate NonEmpty as}} -> Stream a
cycle as = flip unfold as \ where
  [] -> undefined -- We never use this case anyways.
  (x :: []) -> (x , as)
  (x :: xs) -> (x , xs)
