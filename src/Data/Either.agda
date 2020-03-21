{-# OPTIONS --type-in-type #-}

module Data.Either where

open import Prelude

private
  variable
    A B C D : Set

-- Case analysis for the Either type. If the value is left x, apply the first
-- function to x; if it is right y, apply the second function to y.
either : (A -> C) -> (B -> C) -> A + B -> C
either f g (left x) = f x
either f g (right y) = g y

-- This function is the map operation for Either considered as a bifunctor.
plus : (A -> B) -> (C -> D) -> A + C -> B + D
plus f g = either (left <<< f) (right <<< g)

-- Turns a left into a right and vice-versa.
mirror : A + B -> B + A
mirror = either right left

-- Untags (i.e. removes) the left/right wrapper around a value.
untag : A + A -> A
untag = either identity identity

-- Returns true if the given Either value is a left; false otherwise.
isLeft : A + B -> Bool
isLeft = either (const true) (const false)

-- Returns true if the given Either value is a right; false otherwise.
isRight : A + B -> Bool
isRight = not <<< isLeft

-- Return the contents of a left-value or a default value otherwise.
fromLeft : A -> A + B -> A
fromLeft x = either identity (const x)

-- Return the contents of a right-value or a default value otherwise.
fromRight : B -> A + B -> B
fromRight y = either (const y) identity
