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

private
  floatEq : Float -> Float -> Bool
  floatEq = primFloatEquality

  floatLessThan : Float -> Float -> Bool
  floatLessThan =  primFloatLess

  floatPlus : Float -> Float -> Float
  floatPlus = primFloatPlus

  floatNegate : Float -> Float
  floatNegate = primFloatNegate

  floatMinus : Float -> Float -> Float
  floatMinus = primFloatMinus

  floatTimes : Float -> Float -> Float
  floatTimes = primFloatTimes

  floatDiv : Float -> Float -> Float
  floatDiv = primFloatDiv

  natToFloat : Nat -> Float
  natToFloat = primNatToFloat

NaN : Float
NaN = floatDiv 0.0 0.0

Infinity -Infinity : Float
Infinity = floatDiv 1.0 0.0
-Infinity = floatNegate Infinity

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
  Eq-Float ._==_ = floatEq

  Ord-Float : Ord Float
  Ord-Float .compare x y =
    if x == y then EQ
    else if floatLessThan x y then LT
    else GT

  FromNat-Float : FromNat Float
  FromNat-Float .FromNatConstraint _ = Unit
  FromNat-Float .fromNat n = natToFloat n

  Num-Float : Num Float
  Num-Float .nonzero x = if x == 0.0 then False else True
  Num-Float ._+_ = floatPlus
  Num-Float ._-_ = floatMinus
  Num-Float ._*_ = floatTimes

  FromNeg-Float : FromNeg Float
  FromNeg-Float .FromNegConstraint _ = Unit
  FromNeg-Float .fromNeg n = floatNegate (natToFloat n)

  Signed-Float : Signed Float
  Signed-Float .-_ = floatNegate
  Signed-Float .abs x = if x < 0.0 then - x else x
  Signed-Float .signum x = case compare x 0.0 of \ where
    LT -> -1.0
    EQ -> 0.0
    GT -> 1.0

  Fractional-Float : Fractional Float
  Fractional-Float ._/_ x y = floatDiv x y
