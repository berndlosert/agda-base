{-# OPTIONS --type-in-type #-}

module Data.Bool where

-- The type Bool has two constructors: false and true.
open import Agda.Builtin.Bool public

-- The equivalents of false and true at the type-level are Void and Unit. We
-- record this fact with a Cast instance.
open import Data.Cast
open import Data.Unit
open import Data.Void
instance
  BoolToSet : Cast Bool Set
  BoolToSet .cast true = Unit
  BoolToSet .cast false = Void

-- The fold operation for Bool.
bool : {X : Set} -> X -> X -> Bool -> X
bool x y false = x
bool x y true = y

-- The if/then/else idiom is just bool in disguise.
if_then_else_ : {X : Set} -> Bool -> X -> X -> X
if b then x else y = bool y x b
infix 0 if_then_else_

-- Apart from the identity function, there is one other function of type
-- Bool -> Bool, namely not.
not : Bool -> Bool
not true  = false
not false = true

-- The Boolean "and" operation.
_&&_ : Bool -> Bool -> Bool
true && b = b
false && b = false
infixr 6 _&&_

-- The Boolean "or" operation.
_||_ : Bool -> Bool -> Bool
true || b = true
false || b = b
infixr 5 _||_

-- Bool is a semigroup with respect to && and ||.
open import Data.Semigroup
Semigroup:&& : Semigroup Bool
Semigroup:&& = Semigroup: _&&_
Semigroup:|| : Semigroup Bool
Semigroup:|| = Semigroup: _||_

-- Bool is monoid with respect to && and ||.
open import Data.Monoid
Monoid:&& : Monoid Bool
Monoid:&& = Monoid: {{Semigroup:&&}} true
Monoid:|| : Monoid Bool
Monoid:|| = Monoid: {{Semigroup:||}} false
