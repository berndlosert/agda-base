{-# OPTIONS --type-in-type #-}

module Data.PRNG.Squares where

open import Prelude

open import Data.Bits
open import Data.PRNG
open import Data.Word

-- Squares: A Fast Counter-Based RNG
-- https://arxiv.org/pdf/2004.06278v2.pdf
record Squares : Set where
  constructor squares:
  field ctr key : Word64

private
  squares : Word64 -> Word64 -> Word64
  squares ctr key =
    let
      x0 = ctr * key
      y = x0
      z = y + key
      -- Round 1
      x1 = x0 * x0 + y
      x2 = (shiftR x1 32) :|: (shiftL x1 32)
      -- Round 2
      x3 = x2 * x2 + z
      x4 = (shiftR x3 32) :|: (shiftL x3 32)
    in
      shiftR (x4 * x4 + y) 32

instance
  prngSquares : PRNG Squares
  prngSquares .genNext (squares: ctr key) =
      (n , squares: key ctr')
    where
      ctr' = squares ctr key
      n = word64ToNat ctr'
