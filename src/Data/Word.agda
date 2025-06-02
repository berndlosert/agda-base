module Data.Word where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Bits

-------------------------------------------------------------------------------
-- Word8
-------------------------------------------------------------------------------

postulate
  Word8 : Type

private
  2^8 : Nat
  2^8 = 256

  postulate
    natToWord8 : Nat -> Word8
    word8ToNat : Word8 -> Nat
    word8Eq : Word8 -> Word8 -> Bool
    word8Less : Word8 -> Word8 -> Bool
    word8Or : Word8 -> Word8 -> Word8
    word8Xor : Word8 -> Word8 -> Word8
    word8All : Word8 -> Word8 -> Word8
    word8Shift : Word8 -> Int -> Word8
    word8Rotate : Word8 -> Int -> Word8
    word8Bit : Nat -> Word8
    word8TestBit : Word8 -> Nat -> Bool
    word8IsSigned : Word8 -> Bool
    word8PopCount : Word8 -> Nat
    word8Plus : Word8 -> Word8 -> Word8
    word8Minus : Word8 -> Word8 -> Word8
    word8Negate : Word8 -> Word8
    word8Times : Word8 -> Word8 -> Word8
    word8Power : Word8 -> Nat -> Word8

instance
  FromNat-Word8 : FromNat Word8
  FromNat-Word8 .FromNat.Constraint _ = Unit
  FromNat-Word8 .fromNat n = natToWord8 n

  ToNat-Word8 : ToNat Word8
  ToNat-Word8 .toNat w = word8ToNat w

  Eq-Word8 : Eq Word8
  Eq-Word8 ._==_ = word8Eq

  Ord-Word8 : Ord Word8
  Ord-Word8 ._<_ = word8Less

  Bits-Word8 : Bits Word8
  Bits-Word8 .bitSize _ = 8
  Bits-Word8 .zeroBits = 0x0
  Bits-Word8 .oneBits = 0xFFFFFFFF
  Bits-Word8 .orBits = word8Or
  Bits-Word8 .xorBits = word8Xor
  Bits-Word8 .andBits = word8All
  Bits-Word8 .shift = word8Shift
  Bits-Word8 .rotate = word8Rotate
  Bits-Word8 .bit = word8Bit
  Bits-Word8 .testBit = word8TestBit
  Bits-Word8 .isSigned = word8IsSigned
  Bits-Word8 .popCount = word8PopCount

  Addable-Word8 : Addable Word8
  Addable-Word8 ._+_ = word8Plus

  Multipliable-Word8 : Multipliable Word8
  Multipliable-Word8 ._*_ = word8Times

  Negatable-Word8 : Negatable Word8
  Negatable-Word8 .-_ = word8Negate

  Subtractable-Word8 : Subtractable Word8
  Subtractable-Word8 ._-_ = word8Minus

  Exponentiable-Word8 : Exponentiable Word8
  Exponentiable-Word8 .Power = Nat
  Exponentiable-Word8 ._^_ = word8Power

-------------------------------------------------------------------------------
-- Word16
-------------------------------------------------------------------------------

postulate
  Word16 : Type

private
  2^16 : Nat
  2^16 = 256

  postulate
    natToWord16 : Nat -> Word16
    word16ToNat : Word16 -> Nat
    word16Eq : Word16 -> Word16 -> Bool
    word16Less : Word16 -> Word16 -> Bool
    word16Or : Word16 -> Word16 -> Word16
    word16Xor : Word16 -> Word16 -> Word16
    word16All : Word16 -> Word16 -> Word16
    word16Shift : Word16 -> Int -> Word16
    word16Rotate : Word16 -> Int -> Word16
    word16Bit : Nat -> Word16
    word16TestBit : Word16 -> Nat -> Bool
    word16IsSigned : Word16 -> Bool
    word16PopCount : Word16 -> Nat
    word16Plus : Word16 -> Word16 -> Word16
    word16Minus : Word16 -> Word16 -> Word16
    word16Negate : Word16 -> Word16
    word16Times : Word16 -> Word16 -> Word16
    word16Power : Word16 -> Nat -> Word16

instance
  FromNat-Word16 : FromNat Word16
  FromNat-Word16 .FromNat.Constraint _ = Unit
  FromNat-Word16 .fromNat n = natToWord16 n

  ToNat-Word16 : ToNat Word16
  ToNat-Word16 .toNat w = word16ToNat w

  Eq-Word16 : Eq Word16
  Eq-Word16 ._==_ = word16Eq

  Ord-Word16 : Ord Word16
  Ord-Word16 ._<_ = word16Less

  Bits-Word16 : Bits Word16
  Bits-Word16 .bitSize _ = 16
  Bits-Word16 .zeroBits = 0x0
  Bits-Word16 .oneBits = 0xFFFFFFFF
  Bits-Word16 .orBits = word16Or
  Bits-Word16 .xorBits = word16Xor
  Bits-Word16 .andBits = word16All
  Bits-Word16 .shift = word16Shift
  Bits-Word16 .rotate = word16Rotate
  Bits-Word16 .bit = word16Bit
  Bits-Word16 .testBit = word16TestBit
  Bits-Word16 .isSigned = word16IsSigned
  Bits-Word16 .popCount = word16PopCount

  Addable-Word16 : Addable Word16
  Addable-Word16 ._+_ = word16Plus

  Multipliable-Word16 : Multipliable Word16
  Multipliable-Word16 ._*_ = word16Times

  Negatable-Word16 : Negatable Word16
  Negatable-Word16 .-_ = word16Negate

  Subtractable-Word16 : Subtractable Word16
  Subtractable-Word16 ._-_ = word16Minus

  Exponentiable-Word16 : Exponentiable Word16
  Exponentiable-Word16 .Power = Nat
  Exponentiable-Word16 ._^_ = word16Power

-------------------------------------------------------------------------------
-- Word32
-------------------------------------------------------------------------------

postulate
  Word32 : Type

private
  2^32 : Nat
  2^32 = 4294967296

  postulate
    natToWord32 : Nat -> Word32
    word32ToNat : Word32 -> Nat
    word32Eq : Word32 -> Word32 -> Bool
    word32Less : Word32 -> Word32 -> Bool
    word32Or : Word32 -> Word32 -> Word32
    word32Xor : Word32 -> Word32 -> Word32
    word32All : Word32 -> Word32 -> Word32
    word32Shift : Word32 -> Int -> Word32
    word32Rotate : Word32 -> Int -> Word32
    word32Bit : Nat -> Word32
    word32TestBit : Word32 -> Nat -> Bool
    word32IsSigned : Word32 -> Bool
    word32PopCount : Word32 -> Nat
    word32Plus : Word32 -> Word32 -> Word32
    word32Minus : Word32 -> Word32 -> Word32
    word32Negate : Word32 -> Word32
    word32Times : Word32 -> Word32 -> Word32
    word32Power : Word32 -> Nat -> Word32

instance
  FromNat-Word32 : FromNat Word32
  FromNat-Word32 .FromNat.Constraint _ = Unit
  FromNat-Word32 .fromNat n = natToWord32 n

  ToNat-Word32 : ToNat Word32
  ToNat-Word32 .toNat w = word32ToNat w

  Eq-Word32 : Eq Word32
  Eq-Word32 ._==_ = word32Eq

  Ord-Word32 : Ord Word32
  Ord-Word32 ._<_ = word32Less

  Bits-Word32 : Bits Word32
  Bits-Word32 .bitSize _ = 32
  Bits-Word32 .zeroBits = 0x0
  Bits-Word32 .oneBits = 0xFFFFFFFF
  Bits-Word32 .orBits = word32Or
  Bits-Word32 .xorBits = word32Xor
  Bits-Word32 .andBits = word32All
  Bits-Word32 .shift = word32Shift
  Bits-Word32 .rotate = word32Rotate
  Bits-Word32 .bit = word32Bit
  Bits-Word32 .testBit = word32TestBit
  Bits-Word32 .isSigned = word32IsSigned
  Bits-Word32 .popCount = word32PopCount

  Addable-Word32 : Addable Word32
  Addable-Word32 ._+_ = word32Plus

  Multipliable-Word32 : Multipliable Word32
  Multipliable-Word32 ._*_ = word32Times

  Negatable-Word32 : Negatable Word32
  Negatable-Word32 .-_ = word32Negate

  Subtractable-Word32 : Subtractable Word32
  Subtractable-Word32 ._-_ = word32Minus

  Exponentiable-Word32 : Exponentiable Word32
  Exponentiable-Word32 .Power = Nat
  Exponentiable-Word32 ._^_ = word32Power

-------------------------------------------------------------------------------
-- Word64
-------------------------------------------------------------------------------

open import Agda.Builtin.Word public
  using (Word64)

private
  2^64 : Nat
  2^64 = 18446744073709551616

  natToWord64 : Nat -> Word64
  natToWord64 = Agda.Builtin.Word.primWord64FromNat

  word64ToNat : Word64 -> Nat
  word64ToNat = Agda.Builtin.Word.primWord64ToNat

  postulate
    word64Eq : Word64 -> Word64 -> Bool
    word64Less : Word64 -> Word64 -> Bool
    word64Or : Word64 -> Word64 -> Word64
    word64Xor : Word64 -> Word64 -> Word64
    word64All : Word64 -> Word64 -> Word64
    word64Shift : Word64 -> Int -> Word64
    word64Rotate : Word64 -> Int -> Word64
    word64Bit : Nat -> Word64
    word64TestBit : Word64 -> Nat -> Bool
    word64IsSigned : Word64 -> Bool
    word64PopCount : Word64 -> Nat
    word64Plus : Word64 -> Word64 -> Word64
    word64Minus : Word64 -> Word64 -> Word64
    word64Negate : Word64 -> Word64
    word64Times : Word64 -> Word64 -> Word64
    word64Power : Word64 -> Nat -> Word64

instance
  FromNat-Word64 : FromNat Word64
  FromNat-Word64 .FromNat.Constraint _ = Unit
  FromNat-Word64 .fromNat n = natToWord64 n

  ToNat-Word64 : ToNat Word64
  ToNat-Word64 .toNat w = word64ToNat w

  Eq-Word64 : Eq Word64
  Eq-Word64 ._==_ = word64Eq

  Ord-Word64 : Ord Word64
  Ord-Word64 ._<_ = word64Less

  Bits-Word64 : Bits Word64
  Bits-Word64 .bitSize _ = 64
  Bits-Word64 .zeroBits = 0x0
  Bits-Word64 .oneBits = 0xFFFFFFFFFFFFFFFF
  Bits-Word64 .orBits = word64Or
  Bits-Word64 .xorBits = word64Xor
  Bits-Word64 .andBits = word64All
  Bits-Word64 .shift = word64Shift
  Bits-Word64 .rotate = word64Rotate
  Bits-Word64 .bit = word64Bit
  Bits-Word64 .testBit = word64TestBit
  Bits-Word64 .isSigned = word64IsSigned
  Bits-Word64 .popCount = word64PopCount

  Addable-Word64 : Addable Word64
  Addable-Word64 ._+_ = word64Plus

  Multipliable-Word64 : Multipliable Word64
  Multipliable-Word64 ._*_ = word64Times

  Negatable-Word64 : Negatable Word64
  Negatable-Word64 .-_ = word64Negate

  Subtractable-Word64 : Subtractable Word64
  Subtractable-Word64 ._-_ = word64Minus

  Exponentiable-Word64 : Exponentiable Word64
  Exponentiable-Word64 .Power = Nat
  Exponentiable-Word64 ._^_ = word64Power

-------------------------------------------------------------------------------
-- FFI
-------------------------------------------------------------------------------

{-# FOREIGN GHC import Data.Word #-}
{-# FOREIGN GHC import Data.Bits #-}

{-# COMPILE GHC Word8 = type Word8 #-}
{-# COMPILE GHC natToWord8 = fromInteger #-}
{-# COMPILE GHC word8ToNat = toInteger #-}
{-# COMPILE GHC word8Eq = (==) #-}
{-# COMPILE GHC word8Less = (<) #-}
{-# COMPILE GHC word8Or = (.|.) #-}
{-# COMPILE GHC word8Xor = xor #-}
{-# COMPILE GHC word8All = (.&.) #-}
{-# COMPILE GHC word8Shift = \ x i -> shift x (fromIntegral i) #-}
{-# COMPILE GHC word8Rotate = \ x i -> rotate x (fromIntegral i) #-}
{-# COMPILE GHC word8Bit = bit . fromIntegral #-}
{-# COMPILE GHC word8TestBit = \ x i -> testBit x (fromIntegral i) #-}
{-# COMPILE GHC word8IsSigned = isSigned #-}
{-# COMPILE GHC word8PopCount = toInteger . popCount #-}
{-# COMPILE GHC word8Plus = (+) #-}
{-# COMPILE GHC word8Minus = (+) #-}
{-# COMPILE GHC word8Negate = negate #-}
{-# COMPILE GHC word8Times = (*) #-}
{-# COMPILE GHC word8Power = (^) #-}

{-# COMPILE GHC Word16 = type Word16 #-}
{-# COMPILE GHC natToWord16 = fromInteger #-}
{-# COMPILE GHC word16ToNat = toInteger #-}
{-# COMPILE GHC word16Eq = (==) #-}
{-# COMPILE GHC word16Less = (<) #-}
{-# COMPILE GHC word16Or = (.|.) #-}
{-# COMPILE GHC word16Xor = xor #-}
{-# COMPILE GHC word16All = (.&.) #-}
{-# COMPILE GHC word16Shift = \ x i -> shift x (fromIntegral i) #-}
{-# COMPILE GHC word16Rotate = \ x i -> rotate x (fromIntegral i) #-}
{-# COMPILE GHC word16Bit = bit . fromIntegral #-}
{-# COMPILE GHC word16TestBit = \ x i -> testBit x (fromIntegral i) #-}
{-# COMPILE GHC word16IsSigned = isSigned #-}
{-# COMPILE GHC word16PopCount = toInteger . popCount #-}
{-# COMPILE GHC word16Plus = (+) #-}
{-# COMPILE GHC word16Minus = (+) #-}
{-# COMPILE GHC word16Negate = negate #-}
{-# COMPILE GHC word16Times = (*) #-}
{-# COMPILE GHC word16Power = (^) #-}

{-# COMPILE GHC Word32 = type Word32 #-}
{-# COMPILE GHC natToWord32 = fromInteger #-}
{-# COMPILE GHC word32ToNat = toInteger #-}
{-# COMPILE GHC word32Eq = (==) #-}
{-# COMPILE GHC word32Less = (<) #-}
{-# COMPILE GHC word32Or = (.|.) #-}
{-# COMPILE GHC word32Xor = xor #-}
{-# COMPILE GHC word32All = (.&.) #-}
{-# COMPILE GHC word32Shift = \ x i -> shift x (fromIntegral i) #-}
{-# COMPILE GHC word32Rotate = \ x i -> rotate x (fromIntegral i) #-}
{-# COMPILE GHC word32Bit = bit . fromIntegral #-}
{-# COMPILE GHC word32TestBit = \ x i -> testBit x (fromIntegral i) #-}
{-# COMPILE GHC word32IsSigned = isSigned #-}
{-# COMPILE GHC word32PopCount = toInteger . popCount #-}
{-# COMPILE GHC word32Plus = (+) #-}
{-# COMPILE GHC word32Minus = (+) #-}
{-# COMPILE GHC word32Negate = negate #-}
{-# COMPILE GHC word32Times = (*) #-}
{-# COMPILE GHC word32Power = (^) #-}

{-# COMPILE GHC word64Eq = (==) #-}
{-# COMPILE GHC word64Less = (<) #-}
{-# COMPILE GHC word64Or = (.|.) #-}
{-# COMPILE GHC word64Xor = xor #-}
{-# COMPILE GHC word64All = (.&.) #-}
{-# COMPILE GHC word64Shift = \ x i -> shift x (fromIntegral i) #-}
{-# COMPILE GHC word64Rotate = \ x i -> rotate x (fromIntegral i) #-}
{-# COMPILE GHC word64Bit = bit . fromIntegral #-}
{-# COMPILE GHC word64TestBit = \ x i -> testBit x (fromIntegral i) #-}
{-# COMPILE GHC word64IsSigned = isSigned #-}
{-# COMPILE GHC word64PopCount = toInteger . popCount #-}
{-# COMPILE GHC word64Plus = (+) #-}
{-# COMPILE GHC word64Minus = (+) #-}
{-# COMPILE GHC word64Negate = negate #-}
{-# COMPILE GHC word64Times = (*) #-}
{-# COMPILE GHC word64Power = (^) #-}
