{-# OPTIONS --type-in-type #-}

module Data.Bits where

open import Prelude

record Bits (A : Set) : Set where
  infixl 5 _:|:_
  infixl 6 _xor_
  infixl 7 _:&:_
  field
    zeroBits : A
    oneBits : A
    _:|:_ : A -> A -> A
    _xor_ : A -> A -> A
    _:&:_ : A -> A -> A
    shift : A -> Int -> A
    rotate : A -> Int -> A
    bit : Nat -> A
    testBit : A -> Nat -> Bool
    bitSize : A -> Nat
    isSigned : A -> Bool
    popCount : A -> Nat

  complement : A -> A
  complement x = x xor oneBits

  clearBit : A -> Nat -> A
  clearBit x i = x :&: complement (bit i)

  setBit : A -> Nat -> A
  setBit x i = x :|: bit i

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

open Bits {{...}} public
