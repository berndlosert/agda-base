{-# OPTIONS --type-in-type #-}

module Data.Bool.Monoid where

open import Data.Bool.Base
open import Data.Bool.Semigroup
open import Data.Monoid public

Monoid:&& : Monoid Bool
Monoid:&& = Monoid: {{Semigroup:&&}} true

Monoid:|| : Monoid Bool
Monoid:|| = Monoid: {{Semigroup:||}} false
