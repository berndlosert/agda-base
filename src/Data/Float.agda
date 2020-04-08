{-# OPTIONS --type-in-type #-}

module Data.Float where

module Float where
  open import Agda.Builtin.Float public
    using (Float)
    renaming (
      primFloatNumericalEquality to eq;
      primFloatNumericalLess to lt;
      primFloatPlus to add;
      primFloatTimes to mul;
      primFloatMinus to sub;
      primFloatDiv to div;
      primNatToFloat to fromNat;
      primShowFloat to show;
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

  --fromInt : Int -> Float
  --fromInt (pos n) = fromNat n
  --fromInt (negsuc n) = - (fromNat n) - 1.0

open Float public
  using (Float)

open import Prelude

instance
  eqFloat : Eq Float
  eqFloat ._==_ = Float.eq

  ordFloat : Ord Float
  ordFloat ._<_ = Float.lt

  semiringFloat : Semiring Float
  semiringFloat .zero = 0.0
  semiringFloat .one = 1.0
  semiringFloat ._+_ = Float.add
  semiringFloat ._*_ = Float.mul

  ringFloat : Ring Float
  ringFloat ._-_ = Float.sub

  numFloat : Num Float
  numFloat .Nonzero x = if x == 0.0 then Void else Unit
  numFloat ._/_ x y = Float.div x y
  numFloat ._%_ _ _ = 0.0
