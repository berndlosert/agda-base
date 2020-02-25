{-# OPTIONS --type-in-type #-}

module Data.Vector where

open import Prelude

splitAt : forall m {n X} -> Vec X (m + n) -> Vec X m * Vec X n
splitAt zero xs = Pair: [] xs
splitAt (suc k) (x :: xs) with (splitAt k xs)
... | (Pair: tk dr) = Pair: (x :: tk) dr
