{-# OPTIONS --type-in-type #-}

module Data.Void.Semigroup where

open import Data.Semigroup public
open import Data.Void.Base

instance
  Semigroup:Void : Semigroup Void
  Semigroup:Void = Semigroup: \ ()
