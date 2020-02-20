{-# OPTIONS --type-in-type #-}

module Data.String.Semigroup where

open import Data.Semigroup public
open import Data.String.Base

instance
  Semigroup:String : Semigroup String
  Semigroup:String = Semigroup: _++_
