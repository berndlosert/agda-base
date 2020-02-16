{-# OPTIONS --type-in-type #-}

module Data.Maybe where

open import Data.Maybe.Base public
  hiding (module Maybe)

module Maybe where

  -- This function takes a default value and and Maybe value. If the Maybe is
  -- nothing, it returns the default value; otherwise, it returns the value
  -- contained in the Maybe.

  getOrElse : forall {X} -> X -> Maybe X -> X
  getOrElse x nothing = x
  getOrElse _ (just x) = x
