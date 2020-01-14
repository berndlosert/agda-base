{-# OPTIONS --type-in-type #-}

module Data.Maybe where

open import Data.Maybe.Base public
  hiding (module Maybe)

-- The from function takes a default value and and Maybe value. If the Maybe
-- is nothing, it returns the default value; otherwise, it returns the value
-- contained in the Maybe.

fromMaybe : forall {X} -> X -> Maybe X -> X
fromMaybe x nothing = x
fromMaybe _ (just x) = x
