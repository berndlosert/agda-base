{-# OPTIONS --type-in-type #-}

module Data.PRNG.MinStd where

open import Prelude

open import Data.PRNG
open import Data.Word

record MinStd : Set where
  constructor minStd:
  field state : Word32

instance
  prngMinStd : PRNG MinStd
  prngMinStd .genNext (minStd: s) = (s' , minStd: (natToWord32 s'))
    where s' = word32ToNat s * 48271 % 0x7fffffff
