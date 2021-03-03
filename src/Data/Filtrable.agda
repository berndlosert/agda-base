{-# OPTIONS --type-in-type #-}

module Data.Filtrable where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c : Set
    f t : Set -> Set

-------------------------------------------------------------------------------
-- Filtrable
-------------------------------------------------------------------------------

record Filtrable (t : Set -> Set) where
  field
    filter : (a -> Bool) -> t a -> t a
    filterA : {{_ : Traversable t}} {{_ : Applicative f}}
      (a -> f Bool) -> t a -> f (t a)
    mapMaybe : (a -> Maybe b) -> t a -> t b
    mapMaybeA : {{_ : Traversable t}} {{_ : Applicative f}}
      (a -> f (Maybe b)) -> t a -> f (t b)
    mapEither : (a -> Either b c) -> t a -> t b * t c
    mapEitherA : {{_ : Traversable t}} {{_ : Applicative f}}
      (a -> f (Either b c)) -> t a -> f (t b * t c)

open Filtrable {{...}} public
