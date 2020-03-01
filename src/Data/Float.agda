{-# OPTIONS --type-in-type #-}

module Data.Float where

open import Prelude hiding (fromNat)

open import Agda.Builtin.Float public
  renaming (
    primNatToFloat to fromNat;
    primRound to round;
    primFloor to floor;
    primCeiling to ceil;
    primExp to exp;
    primLog to log;
    primSin to sin;
    primCos to cos;
    primTan to tan;
    primASin to asin;
    primACos to acos;
    primATan to atan;
    primATan2 to atan2
  )

fromInt : Int -> Float
fromInt (pos n) = fromNat n
fromInt (negsuc n) = - (fromNat n) - 1.0
