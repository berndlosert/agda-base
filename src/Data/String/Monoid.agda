{-# OPTIONS --type-in-type #-}

module Data.String.Monoid where

open import Data.Monoid public
open import Data.String.Base
open import Data.String.Semigroup

instance
  Monoid:String : Monoid String
  Monoid:String = Monoid: ""
