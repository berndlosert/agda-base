{-# OPTIONS --type-in-type #-}

module Data.Bool.Semigroup where

open import Data.Bool.Base
open import Data.Semigroup public

Semigroup:&& : Semigroup Bool
Semigroup:&& = Semigroup: _&&_

Semigroup:|| : Semigroup Bool
Semigroup:|| = Semigroup: _||_
