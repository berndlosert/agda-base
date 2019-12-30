{-# OPTIONS --type-in-type #-}

module Data.Float where

-- Floating point numbers.

open import Agda.Builtin.Float public
  using (Float)

module Float where

  import Agda.Builtin.Float as Builtin
      
  -- Convert a Nat to a Float. 

  fromNat = Builtin.primNatToFloat

  -- Use _+_ to add Float values. 

  open import Notation.Add

  instance
    Add:Float : Add Float
    Add:Float = Add: Builtin.primFloatPlus
    
  -- Use _-_ to subtract Float values.

  open import Notation.Sub

  instance
    Sub:Float : Sub Float
    Sub:Float = Sub: Builtin.primFloatMinus

  -- Use _*_ to multiply Float values.

  open import Notation.Mul

  instance
    Mul:Float : Mul Float
    Mul:Float = Mul: Builtin.primFloatTimes

  -- Use -_ to negate Float values.

  open import Notation.Negative

  instance
    Negation:Float : Negation Float
    Negation:Float = Negation: Builtin.primFloatNegate

  -- Use _/_ to divide Float values.

  open import Data.Unit
  open import Notation.Div

  instance
    Div:Float : Div Float
    Div:Float = record {
        Constraint = \ _ -> Unit;
        _/_ = \ x y -> Builtin.primFloatDiv x y
      }

  -- Equality of Float values.

  open import Data.Eq

  instance
    Eq:Float : Eq Float
    Eq:Float = Eq: Builtin.primFloatNumericalEquality

  -- Compare Float values. 

  open import Data.Ord

  instance
    Ord:Float : Ord Float
    Ord:Float = Ord: Builtin.primFloatNumericalLess 

  -- Pretty-print Float values. 

  toString = Builtin.primShowFloat

  -- Mathematical functions that work with Float values.

  round = Builtin.primRound
  floor = Builtin.primFloor
  ceil = Builtin.primCeiling
  exp = Builtin.primExp
  log = Builtin.primLog
  sin = Builtin.primSin
  cos = Builtin.primCos
  tan = Builtin.primTan
  asin = Builtin.primASin
  acos = Builtin.primACos
  atan = Builtin.primATan
  atan2 = Builtin.primATan2

  -- Convert an Int to a Float.

  open import Data.Int

  fromInt : Int -> Float
  fromInt (pos n) = fromNat n 
  fromInt (negsuc n) = - (fromNat n) - 1.0

open Float public
  using (
    Add:Float; 
    Sub:Float;
    Mul:Float;
    Negation:Float;
    Div:Float;
    Eq:Float;
    Ord:Float
  )
