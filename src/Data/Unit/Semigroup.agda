{-# OPTIONS --type-in-type #-}

module Data.Unit.Semigroup where

open import Data.Semigroup public
open import Data.Unit.Base

instance
  Semigroup:Unit : Semigroup Unit
  Semigroup:Unit = Semigroup: \ _ _ -> tt
