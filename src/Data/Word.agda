{-# OPTIONS --type-in-type #-}

module Data.Word where

open import Prelude

open import Data.Bits

--------------------------------------------------------------------------------
-- Word32
--------------------------------------------------------------------------------

postulate
  Word32 : Set
  word32ToNat : Word32 -> Nat
  natToWord32 : Nat -> Word32

private
  2^32 : Nat
  2^32 = 4294967296

  postulate
    primEqWord32 : Word32 -> Word32 -> Bool
    primLessThanWord32 : Word32 -> Word32 -> Bool
    primOrWord32 : Word32 -> Word32 -> Word32
    primXorWord32 : Word32 -> Word32 -> Word32
    primAndWord32 : Word32 -> Word32 -> Word32
    primShiftWord32 : Word32 -> Int -> Word32
    primRotateWord32 : Word32 -> Int -> Word32
    primBitWord32 : Nat -> Word32
    primTestBitWord32 : Word32 -> Nat -> Bool
    primIsSignedWord32 : Word32 -> Bool
    primPopCountWord32 : Word32 -> Nat

instance
  fromNatWord32 : FromNat Word32
  fromNatWord32 = record {
      Constraint = const Unit;
      fromNat = \ n -> natToWord32 n
    }

  eqWord32 : Eq Word32
  eqWord32 ._==_ = primEqWord32

  ordWord32 : Ord Word32
  ordWord32 ._<_ = primLessThanWord32

  bitsWord32 : Bits Word32
  bitsWord32 .bitSize _ = 32
  bitsWord32 .zeroBits = 0x0
  bitsWord32 .oneBits = 0xFFFFFFFF
  bitsWord32 ._:|:_ = primOrWord32
  bitsWord32 ._xor_ = primXorWord32
  bitsWord32 ._:&:_ = primAndWord32
  bitsWord32 .shift = primShiftWord32
  bitsWord32 .rotate = primRotateWord32
  bitsWord32 .bit = primBitWord32
  bitsWord32 .testBit = primTestBitWord32
  bitsWord32 .isSigned = primIsSignedWord32
  bitsWord32 .popCount = primPopCountWord32

  additionWord32 : Addition Word32
  additionWord32 ._+_ x y = natToWord32 $
    (word32ToNat x + word32ToNat y) % 2^32

  multiplicationWord32 : Multiplication Word32
  multiplicationWord32 ._*_ x y = natToWord32 $
    (word32ToNat x * word32ToNat y) % 2^32

--------------------------------------------------------------------------------
-- Word64
--------------------------------------------------------------------------------

open import Agda.Builtin.Word public
  using (Word64)
  renaming (
    primWord64ToNat to word64ToNat;
    primWord64FromNat to natToWord64
  )

private
  2^64 : Nat
  2^64 = 18446744073709551616

  postulate
    primEqWord64 : Word64 -> Word64 -> Bool
    primLessThanWord64 : Word64 -> Word64 -> Bool
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

  eqWord64 : Eq Word64
  eqWord64 ._==_ = primEqWord64

  ordWord64 : Ord Word64
  ordWord64 ._<_ = primLessThanWord64

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

  additionWord64 : Addition Word64
  additionWord64 ._+_ x y = natToWord64 $
    (word64ToNat x + word64ToNat y) % 2^64

  multiplicationWord64 : Multiplication Word64
  multiplicationWord64 ._*_ x y = natToWord64 $
    (word64ToNat x * word64ToNat y) % 2^64

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

{-# FOREIGN GHC import Data.Word #-}
{-# FOREIGN GHC import Data.Bits #-}

{-# COMPILE GHC Word32 = type Word32 #-}
{-# COMPILE GHC primEqWord32 = \ x y -> x == y #-}
{-# COMPILE GHC primLessThanWord32 = \ x y -> x < y #-}
{-# COMPILE GHC primOrWord32 = \ x y -> x .|. y #-}
{-# COMPILE GHC primXorWord32 = \ x y -> x `xor` y #-}
{-# COMPILE GHC primAndWord32 = \ x y -> x .&. y #-}
{-# COMPILE GHC primShiftWord32 = \ x i -> shift x (fromIntegral i) #-}
{-# COMPILE GHC primRotateWord32 = \ x i -> rotate x (fromIntegral i) #-}
{-# COMPILE GHC primBitWord32 = \ i -> bit (fromIntegral i) #-}
{-# COMPILE GHC primTestBitWord32 = \ x i -> testBit x (fromIntegral i) #-}
{-# COMPILE GHC primIsSignedWord32 = isSigned #-}
{-# COMPILE GHC primPopCountWord32 = toInteger . popCount #-}

{-# COMPILE GHC primEqWord64 = \ x y -> x == y #-}
{-# COMPILE GHC primLessThanWord64 = \ x y -> x < y #-}
{-# COMPILE GHC primOrWord64 = \ x y -> x .|. y #-}
{-# COMPILE GHC primXorWord64 = \ x y -> x `xor` y #-}
{-# COMPILE GHC primAndWord64 = \ x y -> x .&. y #-}
{-# COMPILE GHC primShiftWord64 = \ x i -> shift x (fromIntegral i) #-}
{-# COMPILE GHC primRotateWord64 = \ x i -> rotate x (fromIntegral i) #-}
{-# COMPILE GHC primBitWord64 = \ i -> bit (fromIntegral i) #-}
{-# COMPILE GHC primTestBitWord64 = \ x i -> testBit x (fromIntegral i) #-}
{-# COMPILE GHC primIsSignedWord64 = isSigned #-}
{-# COMPILE GHC primPopCountWord64 = toInteger . popCount #-}
