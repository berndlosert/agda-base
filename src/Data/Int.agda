{-# OPTIONS --type-in-type #-}

module Data.Int where

open import Prelude

postulate
  Int64 : Set
  intToInt64 : Int -> Int64
  int64ToInt : Int64 -> Int

{-# COMPILE GHC Int64 = type Int #-}
{-# COMPILE GHC intToInt64 = fromInteger #-}
{-# COMPILE GHC int64ToInt = toInteger #-}
