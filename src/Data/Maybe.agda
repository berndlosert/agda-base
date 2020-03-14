{-# OPTIONS --type-in-type #-}

module Data.Maybe where

open import Prelude

private
  variable
    X Y : Set

-- The maybe function takes a default value, a function, and a Maybe value. If
-- the Maybe value is nothing, the function returns the default value.
-- Otherwise, it applies the function to the value inside the just and returns
-- the result.
maybe : Y -> (X -> Y) -> Maybe X -> Y
maybe y f nothing = y
maybe y f (just x) = f x

-- The fromMaybe function takes a default value and and Maybe value. If the
-- Maybe is nothing, it returns the default values; otherwise, it returns the
-- value contained in the Maybe.
fromMaybe : X -> Maybe X -> X
fromMaybe = flip maybe id

-- Maybe produce a left, otherwise produce a right.
maybeToLeft : Y -> Maybe X -> X + Y
maybeToLeft y = maybe (right y) left

-- Maybe produce a right, otherwise produce a left.
maybeToRight : Y -> Maybe X -> Y + X
maybeToRight y = maybe (left y) right

-- This function returns an empty list when given nothing or the singleton
-- list [ x ] when given just x.
maybeToList : Maybe X -> List X
maybeToList = maybe [] [_]

-- The listToMaybe function returns nothing on an empty list or just x where x
-- is the first element of the list.
listToMaybe : List X -> Maybe X
listToMaybe [] = nothing
listToMaybe (x :: _) = just x
