{-# OPTIONS --type-in-type #-}

module Data.Float where

open import Agda.Builtin.Float public
  using (Float)
  renaming (
    primNatToFloat to natToFloat;
    primFloatSqrt to sqrt;
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

open import Data.Bool
open import Data.Ord
open import Data.Int
open import Data.Num
open import Data.Unit
open import Data.Void

instance
  eqFloat : Eq Float
  eqFloat ._==_ = Agda.Builtin.Float.primFloatNumericalEquality

  ordFloat : Ord Float
  ordFloat ._<_ = Agda.Builtin.Float.primFloatNumericalLess

  semiringFloat : Semiring Float
  semiringFloat .zero = 0.0
  semiringFloat .one = 1.0
  semiringFloat ._+_ = Agda.Builtin.Float.primFloatPlus
  semiringFloat ._*_ = Agda.Builtin.Float.primFloatTimes

  ringFloat : Ring Float
  ringFloat ._-_ = Agda.Builtin.Float.primFloatMinus

  numFloat : Num Float
  numFloat .Nonzero x = if x == 0.0 then Void else Unit
  numFloat ._/_ x y = Agda.Builtin.Float.primFloatDiv x y
  numFloat ._%_ _ _ = 0.0

intToFloat : Int -> Float
intToFloat (pos n) = natToFloat n
intToFloat (negsuc n) = - (natToFloat n) - 1.0


