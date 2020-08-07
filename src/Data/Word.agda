module Data.Word where

open import Prelude

open import Data.Bits

-------------------------------------------------------------------------------
-- Word32
-------------------------------------------------------------------------------

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
  FromNat-Word32 : FromNat Word32
  FromNat-Word32 = record {
      Constraint = const Unit;
      fromNat = λ n -> natToWord32 n
    }

  Eq-Word32 : Eq Word32
  Eq-Word32 ._==_ = primEqWord32

  Ord-Word32 : Ord Word32
  Ord-Word32 ._<_ = primLessThanWord32

  Bits-Word32 : Bits Word32
  Bits-Word32 .bitSize _ = 32
  Bits-Word32 .zeroBits = 0x0
  Bits-Word32 .oneBits = 0xFFFFFFFF
  Bits-Word32 ._:|:_ = primOrWord32
  Bits-Word32 ._xor_ = primXorWord32
  Bits-Word32 ._:&:_ = primAndWord32
  Bits-Word32 .shift = primShiftWord32
  Bits-Word32 .rotate = primRotateWord32
  Bits-Word32 .bit = primBitWord32
  Bits-Word32 .testBit = primTestBitWord32
  Bits-Word32 .isSigned = primIsSignedWord32
  Bits-Word32 .popCount = primPopCountWord32

  Addition-Word32 : Addition Word32
  Addition-Word32 ._+_ x y = natToWord32 $
    (word32ToNat x + word32ToNat y) % 2^32

  Multiplication-Word32 : Multiplication Word32
  Multiplication-Word32 ._*_ x y = natToWord32 $
    (word32ToNat x * word32ToNat y) % 2^32

-------------------------------------------------------------------------------
-- Word64
-------------------------------------------------------------------------------

postulate Word64 : Set

{-# BUILTIN WORD64 Word64 #-}

private
  2^64 : Nat
  2^64 = 18446744073709551616

  primitive
    primWord64ToNat : Word64 -> Nat
    primWord64FromNat : Nat -> Word64

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

word64ToNat = primWord64ToNat
natToWord64 = primWord64FromNat

instance
  FromNat-Word64 : FromNat Word64
  FromNat-Word64 = record {
      Constraint = const Unit;
      fromNat = λ n -> natToWord64 n
    }

  Eq-Word64 : Eq Word64
  Eq-Word64 ._==_ = primEqWord64

  Ord-Word64 : Ord Word64
  Ord-Word64 ._<_ = primLessThanWord64

  Bits-Word64 : Bits Word64
  Bits-Word64 .bitSize _ = 64
  Bits-Word64 .zeroBits = 0x0
  Bits-Word64 .oneBits = 0xFFFFFFFFFFFFFFFF
  Bits-Word64 ._:|:_ = primOrWord64
  Bits-Word64 ._xor_ = primXorWord64
  Bits-Word64 ._:&:_ = primAndWord64
  Bits-Word64 .shift = primShiftWord64
  Bits-Word64 .rotate = primRotateWord64
  Bits-Word64 .bit = primBitWord64
  Bits-Word64 .testBit = primTestBitWord64
  Bits-Word64 .isSigned = primIsSignedWord64
  Bits-Word64 .popCount = primPopCountWord64

  Addition-Word64 : Addition Word64
  Addition-Word64 ._+_ x y = natToWord64 $
    (word64ToNat x + word64ToNat y) % 2^64

  Multiplication-Word64 : Multiplication Word64
  Multiplication-Word64 ._*_ x y = natToWord64 $
    (word64ToNat x * word64ToNat y) % 2^64

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

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
