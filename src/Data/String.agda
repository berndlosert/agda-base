{-# OPTIONS --type-in-type #-}

module Data.String where

open import Data.String.Base public

module String where
  open import Data.String.Api public
    hiding (
      Semigroup:String;
      Monoid:String
    )

open import Data.String.Api public
  using (
    Semigroup:String;
    Monoid:String
  )
