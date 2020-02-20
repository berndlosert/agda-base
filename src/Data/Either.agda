{-# OPTIONS --type-in-type #-}

module Data.Either where

open import Data.Either.Applicative public
open import Data.Either.Base public
open import Data.Either.Functor public
open import Data.Either.Monad public

module Either where

  open import Control.Monad
  open import Data.Bool.Base
  open import Data.List
  open import Data.Maybe.Base
  open import Data.Pair

  private
    variable
      X Y : Set

  ------------------------------------------------------------------------------
  -- Overview
  ------------------------------------------------------------------------------

  fromLeft : X + Y -> Maybe X
  fromRight : X + Y -> Maybe Y

  lefts : List (Either X Y) -> List X
  rights : List (Either X Y) -> List Y
  partition : List (Either X Y) -> List X * List Y

  isLeft : Either X Y -> Bool
  isRight : Either X Y -> Bool

  note : X -> Maybe Y -> Either X Y

  ------------------------------------------------------------------------------
  -- Details
  ------------------------------------------------------------------------------

  fromLeft (left x) = just x
  fromLeft _ = nothing

  fromRight (right y) = just y
  fromRight _ = nothing

  lefts [] = []
  lefts (left x :: rest) = x :: lefts rest
  lefts (right y :: rest) = lefts rest

  rights [] = []
  rights (left x :: rest) = rights rest
  rights (right y :: rest) = y :: rights rest

  partition = foldr (either l r) (Pair: [] [])
    where
      l : _
      l a p = Pair: (a :: fst p) (snd p)
      r : _
      r a p = Pair: (fst p) (a :: snd p)

  isLeft (left _) = true
  isLeft _ = false

  isRight (right _) = true
  isRight _ = false

  note x nothing = left x
  note x (just y) = right y
