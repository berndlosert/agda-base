{-# OPTIONS --type-in-type #-}

module Data.Decimal where

open import Data.Decimal.Base public

module Decimal where
  open import Data.Decimal.Api public
    hiding (
      Add:Decimal;
      Number:Decimal
    )

open import Data.Decimal.Api public
  using (
    Add:Decimal;
    Number:Decimal
  )
