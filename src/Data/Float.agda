{-# OPTIONS --type-in-type #-}

module Data.Float where

open import Agda.Builtin.Float public using (Float)
open import Agda.Builtin.Float public renaming (primNatToFloat to fromNat)
open import Agda.Builtin.Float public renaming (primFloatSqrt to sqrt)
open import Agda.Builtin.Float public renaming (primRound to round)
open import Agda.Builtin.Float public renaming (primFloor to floor)
open import Agda.Builtin.Float public renaming (primCeiling to ceil)
open import Agda.Builtin.Float public renaming (primExp to exp)
open import Agda.Builtin.Float public renaming (primLog to log)
open import Agda.Builtin.Float public renaming (primSin to sin)
open import Agda.Builtin.Float public renaming (primCos to cos)
open import Agda.Builtin.Float public renaming (primTan to tan)
open import Agda.Builtin.Float public renaming (primASin to asin)
open import Agda.Builtin.Float public renaming (primACos to acos)
open import Agda.Builtin.Float public renaming (primATan to atan)
open import Agda.Builtin.Float public renaming (primATan2 to atan2)
open import Data.Bool using (if_then_else_)
open import Data.Division public using (Division; Nonzero; _/_; _%_)
open import Data.Eq using (Eq)
open import Data.Eq public using (Eq; _==_; _/=_)
open import Data.Int using (Int; pos; negsuc)
open import Data.Ord using (Ord)
open import Data.Ord public using (compare; LT; EQ; GT)
open import Data.Ord public using (_<_; _<=_; _>_; _>=_)
open import Data.Ord public using (min; max; comparing)
open import Data.Ring using (Ring)
open import Data.Ring public using (-_; _-_)
open import Data.Semiring using (Semiring; zero; one)
open import Data.Semiring public using (_+_; _*_)
open import Data.Unit using (Unit)
open import Data.Void using (Void)

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
  ringFloat .-_ = Agda.Builtin.Float.primFloatNegate

  divisionFloat : Division Float
  divisionFloat .Nonzero x = if x == 0.0 then Void else Unit
  divisionFloat ._/_ x y = Agda.Builtin.Float.primFloatDiv x y
  divisionFloat ._%_ _ _ = 0.0

fromInt : Int -> Float
fromInt (pos n) = fromNat n
fromInt (negsuc n) = - (fromNat n) - 1.0
