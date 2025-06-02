module Data.Bits where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Bits
-------------------------------------------------------------------------------

record Bits (a : Type) : Type where
  field
    bitSize : a -> Nat
    zeroBits : a
    oneBits : a
    orBits : a -> a -> a
    xorBits : a -> a -> a
    andBits : a -> a -> a
    shift : a -> Int -> a
    rotate : a -> Int -> a
    bit : Nat -> a
    testBit : a -> Nat -> Bool
    isSigned : a -> Bool
    popCount : a -> Nat

  complement : a -> a
  complement x = xorBits x oneBits

  clearBit : a -> Nat -> a
  clearBit x i = andBits x (complement (bit i))

  setBit : a -> Nat -> a
  setBit x i = orBits x (bit i)

  assignBit : a -> Nat -> Bool -> a
  assignBit b n true = setBit b n
  assignBit b n false = clearBit b n

  notBit : a -> Nat -> a
  notBit x i = xorBits x (bit i)

  shiftL : a -> Nat -> a
  shiftL x i = shift x (pos i)

  shiftR : a -> Nat -> a
  shiftR x i = shift x (neg i)

  rotateL : a -> Nat -> a
  rotateL x i = rotate x (pos i)

  rotateR : a -> Nat -> a
  rotateR x i = rotate x (neg i)

  countLeadingZeros : a -> Nat
  countLeadingZeros x =
      let n = bitSize x - 1 in n - (go n)
    where
      go : Nat -> Nat
      go 0 = 0
      go n@(suc n-1) = if testBit x n then n else go n-1

  countTrailingZeros : a -> Nat
  countTrailingZeros x =
     let n = bitSize x - 1 in go n 0
    where
      go : Nat -> Nat -> Nat
      go 0 n = n
      go (suc m) n =
        if testBit x n then n
        else go m (n + 1)

open Bits {{...}} public
