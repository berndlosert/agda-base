module Data.Float where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude as Prelude hiding (fromNat)

open import Agda.Builtin.Float

-------------------------------------------------------------------------------
-- Literals
-------------------------------------------------------------------------------

instance
  _ = FromNat-Float

-------------------------------------------------------------------------------
-- Float primitives
-------------------------------------------------------------------------------

divide : Float -> Float -> Float
divide = primFloatDiv

NaN : Float
NaN = divide 0.0 0.0

infinity : Float
infinity = divide 1.0 0.0

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

fromNat : Nat -> Float
fromNat n = Prelude.fromNat n

fromNat1 : Nat1 -> Float
fromNat1 (suc n) = fromNat (suc n)

fromInt : Int -> Float
fromInt (pos n) = fromNat n
fromInt (negsuc n) = - (fromNat (suc n))
