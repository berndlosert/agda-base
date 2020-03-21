{-# OPTIONS --type-in-type #-}

module Data.Pair where

open import Prelude

private
  variable
    A B C D : Set

split : (A -> B) -> (A -> C) -> A -> B * C
split f g a = (f a , g a)

cross : (A -> B) -> (C -> D) -> A * C -> B * D
cross f g = split (f <<< fst) (g <<< snd)

swap : A * B -> B * A
swap = split snd fst

dupe : A -> A * A
dupe = split identity identity

apply : (A -> B) * A -> B
apply = uncurry _$_
