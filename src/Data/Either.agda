{-# OPTIONS --type-in-type #-}

module Data.Either where

open import Prelude

-- Case analysis for the Either type. If the value is left x, apply the first
-- function to x; if it is right y, apply the second function to y.
either : {X Y Z : Set} -> (X -> Z) -> (Y -> Z) -> X + Y -> Z
either f g (left x) = f x
either f g (right y) = g y

-- This function is the map operation for Either considered as a bifunctor.
plus : forall {X X' Y Y'} -> (X -> Y) -> (X' -> Y') -> X + X' -> Y + Y'
plus f g = either (left <<< f) (right <<< g)

-- Turns a left into a right and vice-versa.
mirror : forall {X Y} -> X + Y -> Y + X
mirror = either right left

-- Untags (i.e. removes) the left/right wrapper around a value.
untag : forall {X} -> X + X -> X
untag = either id id

-- Returns true if the given Either value is a left; false otherwise.
isLeft : forall {X Y} -> Either X Y -> Bool
isLeft = either (const true) (const false)

-- Returns true if the given Either value is a right; false otherwise.
isRight : forall {X Y} -> Either X Y -> Bool
isRight = not <<< isLeft

-- Return the contents of a left-value or a default value otherwise.
fromLeft : forall {X Y} -> X -> X + Y -> X
fromLeft x = either id (const x)

-- Return the contents of a right-value or a default value otherwise.
fromRight : forall {X Y} -> Y -> X + Y -> Y
fromRight y = either (const y) id
