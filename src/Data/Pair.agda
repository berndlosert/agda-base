{-# OPTIONS --type-in-type #-}

module Data.Pair where

open import Prelude

split : {X Y Z : Set} -> (X -> Y) -> (X -> Z) -> X -> Y * Z
split f g x = Pair: (f x) (g x)

cross : forall {X X' Y Y'} -> (X -> Y) -> (X' -> Y') -> X * X' -> Y * Y'
cross f g = split (f <<< fst) (g <<< snd)

swap : forall {X Y} -> X * Y -> Y * X
swap = split snd fst

dupe : forall {X} -> X -> X * X
dupe = split id id

apply : forall {X Y} -> (X -> Y) * X -> Y
apply = uncurry _$_
