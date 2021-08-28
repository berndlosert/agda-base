{-# OPTIONS --type-in-type #-}

module Data.Float where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Agda.Builtin.Float

-------------------------------------------------------------------------------
-- Float primitives
-------------------------------------------------------------------------------

NaN : Float
NaN = primFloatDiv 0.0 0.0

infinity : Float
infinity = primFloatDiv 1.0 0.0

sqrt : Float -> Float
sqrt = primFloatSqrt

round : Float -> Maybe Int
round = primFloatRound

floor : Float -> Maybe Int
floor = primFloatFloor

ceil : Float -> Maybe Int
ceil = primFloatCeiling

exp : Float -> Float
exp = primFloatExp

log : Float -> Float
log = primFloatLog

sin : Float -> Float
sin = primFloatSin

cos : Float -> Float
cos = primFloatCos

tan : Float -> Float
tan = primFloatTan

asin : Float -> Float
asin = primFloatASin

acos : Float -> Float
acos = primFloatACos

atan : Float -> Float
atan = primFloatATan

atan2 : Float -> Float -> Float
atan2 = primFloatATan2

sinh : Float -> Float
sinh = primFloatSinh

cosh : Float -> Float
cosh = primFloatCosh

tanh : Float -> Float
tanh = primFloatTanh

asinh : Float -> Float
asinh = primFloatASinh

acosh : Float -> Float
acosh = primFloatACosh

atanh : Float -> Float
atanh = primFloatATanh

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Eq-Float : Eq Float
  Eq-Float ._==_ = primFloatEquality

  Ord-Float : Ord Float
  Ord-Float .compare x y =
    if x == y then EQ
    else if primFloatLess x y then LT
    else GT

  FromNat-Float : FromNat Float
  FromNat-Float .FromNatConstraint _ = Unit
  FromNat-Float .fromNat n = primNatToFloat n

  Neg-Float : Neg Float
  Neg-Float .NegConstraint _ = Unit
  Neg-Float .neg n = primFloatNegate (primNatToFloat n)

  Validation-Positive-Float : Validation Positive Float
  Validation-Positive-Float .validate _ x = x > 0.0

  Validation-NonZero-Float : Validation NonZero Float
  Validation-NonZero-Float .validate _ x = x /= 0.0

  Num-Float : Num Float
  Num-Float ._+_ = primFloatPlus
  Num-Float ._-_ = primFloatMinus
  Num-Float ._*_ = primFloatTimes

  Signed-Float : Signed Float
  Signed-Float .-_ = primFloatNegate
  Signed-Float .abs x = if x < 0.0 then - x else x
  Signed-Float .signum x = case compare x 0.0 of \ where
    LT -> -1.0
    EQ -> 0.0
    GT -> 1.0

  Fractional-Float : Fractional Float
  Fractional-Float ._/_ x y = primFloatDiv x y
