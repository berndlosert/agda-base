{-# OPTIONS --type-in-type #-}

module Data.Bool.Base where

open import Data.Unit
open import Data.Void

infix 0 if_then_else_
infixr 5 _||_
infixr 6 _&&_

-- The type Bool has two constructors: false and true.
open import Agda.Builtin.Bool public

-- The equivalents of false and true at the type-level are Void and Unit.
Assert : Bool -> Set
Assert true = Unit
Assert false = Void

-- The fold operation for Bool.
bool : {X : Set} -> X -> X -> Bool -> X
bool x y false = x
bool x y true = y

-- The if/then/else idiom is just bool in disguise.
if_then_else_ : {X : Set} -> Bool -> X -> X -> X
if b then x else y = bool y x b

-- Apart from the identity function, there is one other function of type
-- Bool -> Bool, namely not.
not : Bool -> Bool
not true  = false
not false = true

-- The Boolean "and" operation.
_&&_ : Bool -> Bool -> Bool
true && b = b
false && b = false

-- The Boolean "or" operation.
_||_ : Bool -> Bool -> Bool
true || b = true
false || b = b
