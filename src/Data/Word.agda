{-# OPTIONS --type-in-type #-}

module Data.Word where

open import Prelude

open import Data.Bits public

open import Agda.Builtin.Word public
  using (Word64)
  renaming (
    primWord64ToNat to word64ToNat;
    primWord64FromNat to natToWord64
  )

private
  postulate
    primOrWord64 : Word64 -> Word64 -> Word64
    primXorWord64 : Word64 -> Word64 -> Word64
    primAndWord64 : Word64 -> Word64 -> Word64
    primShiftWord64 : Word64 -> Int -> Word64
    primRotateWord64 : Word64 -> Int -> Word64
    primBitWord64 : Nat -> Word64
    primTestBitWord64 : Word64 -> Nat -> Bool
    primIsSignedWord64 : Word64 -> Bool
    primPopCountWord64 : Word64 -> Nat

instance
  fromNatWord64 : FromNat Word64
  fromNatWord64 = record {
      Constraint = const Unit;
      fromNat = \ n -> natToWord64 n
    }

  bitsWord64 : Bits Word64
  bitsWord64 .bitSize _ = 64
  bitsWord64 .zeroBits = 0x0
  bitsWord64 .oneBits = 0xFFFFFFFFFFFFFFFF
  bitsWord64 ._:|:_ = primOrWord64
  bitsWord64 ._xor_ = primXorWord64
  bitsWord64 ._:&:_ = primAndWord64
  bitsWord64 .shift = primShiftWord64
  bitsWord64 .rotate = primRotateWord64
  bitsWord64 .bit = primBitWord64
  bitsWord64 .testBit = primTestBitWord64
  bitsWord64 .isSigned = primIsSignedWord64
  bitsWord64 .popCount = primPopCountWord64

{-# FOREIGN GHC import Data.Word #-}
{-# FOREIGN GHC import Data.Bits #-}
{-# COMPILE GHC primOrWord64 = \ x y -> x .|. y #-}
{-# COMPILE GHC primXorWord64 = \ x y -> x `xor` y #-}
{-# COMPILE GHC primAndWord64 = \ x y -> x .&. y #-}
{-# COMPILE GHC primShiftWord64 = \ x i -> shift x (fromIntegral i) #-}
{-# COMPILE GHC primRotateWord64 = \ x i -> rotate x (fromIntegral i) #-}
{-# COMPILE GHC primBitWord64 = \ i -> bit (fromIntegral i) #-}
{-# COMPILE GHC primTestBitWord64 = \ x i -> testBit (fromIntegral i) #-}
{-# COMPILE GHC primIsSignedWord64 = isSigned #-}
{-# COMPILE GHC primPopCountWord64 = toInteger . popCount #-}
