{-# OPTIONS --type-in-type #-}

module Data.Maybe where

open import Prelude

private
  variable
    A B : Set

-- The maybe function takes a default value, a function, and a Maybe value. If
-- the Maybe value is nothing, the function returns the default value.
-- Otherwise, it applies the function to the value inside the just and returns
-- the result.
maybe : B -> (A -> B) -> Maybe A -> B
maybe b f nothing = b
maybe b f (just a) = f a

-- The fromMaybe function takes a default value and and Maybe value. If the
-- Maybe is nothing, it returns the default values; otherwise, it returns the
-- value contained in the Maybe.
fromMaybe : A -> Maybe A -> A
fromMaybe = flip maybe identity

-- Maybe produce a left, otherwise produce a right.
maybeToLeft : B -> Maybe A -> A + B
maybeToLeft b = maybe (right b) left

-- Maybe produce a right, otherwise produce a left.
maybeToRight : B -> Maybe A -> B + A
maybeToRight b = maybe (left b) right

-- This function returns an empty list when given nothing or the singleton
-- list [ x ] when given just x.
maybeToList : Maybe A -> List A
maybeToList = maybe [] singleton

-- The listToMaybe function returns nothing on an empty list or just x where x
-- is the first element of the list.
listToMaybe : List A -> Maybe A
listToMaybe [] = nothing
listToMaybe (a :: _) = just a
