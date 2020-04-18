{-# OPTIONS --type-in-type #-}

module Data.Float where

open import Agda.Builtin.Float public
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

open import Data.Eq
open import Data.Field
open import Data.Monoid
open import Data.Ord
open import Data.Ring
open import Data.Semigroup
open import Data.Semiring
open import Prim

instance
  eqFloat : Eq Float
  eqFloat ._==_ = Agda.Builtin.Float.primFloatNumericalEquality

  ordFloat : Ord Float
  ordFloat ._<_ = Agda.Builtin.Float.primFloatNumericalLess

  semigroupSumFloat : Semigroup (Sum Float)
  semigroupSumFloat ._<>_ x y =
    toSum $ Agda.Builtin.Float.primFloatPlus (fromSum x) (fromSum y)

  semigroupProductFloat : Semigroup (Product Float)
  semigroupProductFloat ._<>_ x y =
    toProduct $ Agda.Builtin.Float.primFloatTimes (fromProduct x) (fromProduct y)

  monoidSumFloat : Monoid (Sum Float)
  monoidSumFloat .mempty = toSum 0.0

  monoidProductFloat : Monoid (Product Float)
  monoidProductFloat .mempty = toProduct 1.0

  semiringFloat : Semiring Float
  semiringFloat .Nonzero x = if x == 0.0 then Void else Unit

  ringFloat : Ring Float
  ringFloat .-_ = Agda.Builtin.Float.primFloatNegate
  ringFloat ._-_ = Agda.Builtin.Float.primFloatMinus

  fieldFloat : Field Float
  fieldFloat ._/_ x y = Agda.Builtin.Float.primFloatDiv x y

intToFloat : Int -> Float
intToFloat (pos n) = natToFloat n
intToFloat (negsuc n) = - (natToFloat n) - 1.0
