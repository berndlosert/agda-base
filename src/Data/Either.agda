{-# OPTIONS --type-in-type #-}

module Data.Either where

open import Data.Either.Applicative public
open import Data.Either.Base public
open import Data.Either.Functor public
open import Data.Either.Monad public

module Either where

  open import Data.Maybe.Base

  private
    variable
      X Y : Set

  ------------------------------------------------------------------------------
  -- Overview
  ------------------------------------------------------------------------------

  fromLeft : X + Y -> Maybe X
  fromRight : X + Y -> Maybe Y
  note : X -> Maybe Y -> Either X Y

  ------------------------------------------------------------------------------
  -- Details
  ------------------------------------------------------------------------------

  fromLeft (left x) = just x
  fromLeft _ = nothing

  fromRight (right y) = just y
  fromRight _ = nothing

  note x nothing = left x
  note x (just y) = right y
