{-# OPTIONS --type-in-type #-}

module Data.Bits where

open import Prelude

record Bits (A : Set) : Set where
  infixl 5 _:|:_
  infixl 6 _xor_
  infixl 7 _:&:_
  field
    bitSize : A -> Nat
    zeroBits : A
    oneBits : A
    _:|:_ : A -> A -> A
    _xor_ : A -> A -> A
    _:&:_ : A -> A -> A
    shift : A -> Int -> A
    rotate : A -> Int -> A
    bit : Nat -> A
    testBit : A -> Nat -> Bool
    isSigned : A -> Bool
    popCount : A -> Nat

  complement : A -> A
  complement x = x xor oneBits

  clearBit : A -> Nat -> A
  clearBit x i = x :&: complement (bit i)

  setBit : A -> Nat -> A
  setBit x i = x :|: bit i

  assignBit : A -> Nat -> Bool -> A
  assignBit b n True = setBit b n
  assignBit b n False = clearBit b n

  notBit : A -> Nat -> A
  notBit x i = x xor (bit i)

  shiftL : A -> Nat -> A
  shiftL x i = shift x (pos i)

  shiftR : A -> Nat -> A
  shiftR x i = shift x (neg i)

  rotateL : A -> Nat -> A
  rotateL x i = rotate x (pos i)

  rotateR : A -> Nat -> A
  rotateR x i = rotate x (neg i)

  countLeadingZeros : A -> Nat
  countLeadingZeros x = bitSize-1 - go bitSize-1
    where
      bitSize-1 : Nat
      bitSize-1 = bitSize x - 1

      go : Nat -> Nat
      go 0 = 0
      go n@(suc n-1) = if testBit x n then n else go n-1

  countTrailingZeros : A -> Nat
  countTrailingZeros x = go bitSize-1 0
    where
      bitSize-1 : Nat
      bitSize-1 = bitSize x - 1

      go : Nat -> Nat -> Nat
      go 0 n = n
      go (suc m) n =
        if testBit x n then n
        else go m (n + 1)

open Bits {{...}} public
