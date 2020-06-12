{-# OPTIONS --type-in-type #-}

module Data.PRNG.SplitMix where

open import Prelude

open import Data.Bits
open import Data.PRNG
open import Data.Word

-- Fast Splittable Pseudorandom Number Generators
-- https://dl.acm.org/doi/10.1145/2660193.2660195

record SplitMix : Set where
  constructor splitMix:
  field
    seed : Word64
    gamma : Word64 -- must be odd

private
  mix64 : Word64 -> Word64
  mix64 z0 = z3
    where
      z1 = (z0 xor (shiftR z0 33)) * 0xff51afd7ed558ccd
      z2 = (z1 xor (shiftR z1 33)) * 0xc4ceb9fe1a85ec53
      z3 = z2 xor (shiftR z2 33)

  mix64variant13 : Word64 -> Word64
  mix64variant13 z0 = z3
    where
      z1 = (z0 xor (shiftR z0 30)) * 0xbf58476d1ce4e5b9
      z2 = (z1 xor (shiftR z1 27)) * 0x94d049bb133111eb
      z3 = z2 xor (shiftR z2 31)

  mixGamma : Word64 -> Word64
  mixGamma z0 =
    let
      z1 = mix64variant13 z0 :|: 1
      n = popCount (z1 xor (shiftR z1 1))
    in
      if n >= 24 then z1 else z1 xor 0xaaaaaaaaaaaaaaaa

instance
  prngSplitMix : PRNG SplitMix
  prngSplitMix .genNext (splitMix: seed gamma) =
      (word64ToNat (mix64 seed') , splitMix: seed' gamma)
    where
      seed' = seed + gamma

  sprngSplitMix : SPRNG SplitMix
  sprngSplitMix .genSplit (splitMix: seed gamma) =
      (splitMix: seed'' gamma , splitMix: (mix64 seed') (mixGamma seed''))
    where
      seed' = seed + gamma
      seed'' = seed' + gamma
