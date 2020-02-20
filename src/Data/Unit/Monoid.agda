{-# OPTIONS --type-in-type #-}

module Data.Unit.Monoid where

open import Data.Monoid public
open import Data.Unit.Base
open import Data.Unit.Semigroup

instance
  Monoid:Unit : Monoid Unit
  Monoid:Unit = Monoid: tt
