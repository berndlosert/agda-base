{-# OPTIONS --type-in-type #-}

module Data.Cast where

-- We use this to specify how to cast types.
record Cast (From To : Set) : Set where
  constructor Cast:
  field
    cast : From -> To

open Cast {{...}} public

castTo : {To From : Set} {{_ : Cast From To}} -> From -> To
castTo = cast
