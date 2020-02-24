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
maybeToLeft : Y -> Maybe X -> Either X Y
maybeToLeft y nothing = right y
maybeToLeft y (just x) = left x

-- Maybe produce a right, otherwise produce a left.
maybeToRight : Y -> Maybe X -> Either Y X
maybeToRight y m = mirror (maybeToLeft y m)

-- This function returns an empty list when given nothing or the singleton
-- list [ x ] when given just x.
maybeToList : Maybe X -> List X
maybeToList nothing = []
maybeToList (just x) = [ x ]


