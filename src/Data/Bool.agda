{-# OPTIONS --type-in-type #-}

module Data.Bool where

-- The type Bool has two constructors: false and true.

open import Agda.Builtin.Bool public

-- The equivalents of false and true at the type-level are Void and Unit. We
-- record this fact with a Cast instance.

open import Data.Unit
open import Data.Void

So : Bool -> Set
So true = Unit
So false = Void

-- The fold operation for Bool.

bool : {X : Set} -> X -> X -> Bool -> X
bool x y false = x
bool x y true = y

-- The if/then/else idiom is just bool in disguise.

infix 0 if_then_else_

if_then_else_ : {X : Set} -> Bool -> X -> X -> X
if b then x else y = bool y x b

-- Apart from the identity function, there is one other function of type
-- Bool -> Bool, namely not.

not : Bool -> Bool
not true  = false
not false = true

-- The Boolean "and" operation.

infixr 6 _&&_

_&&_ : Bool -> Bool -> Bool
true && b = b
false && b = false

-- The Boolean "or" operation.

infixr 5 _||_

_||_ : Bool -> Bool -> Bool
true || b = true
false || b = b

-- Bool is a semigroup with respect to _&&_ and _||_.

open import Data.Semigroup

Semigroup:&& : Semigroup Bool
Semigroup:&& = Semigroup: _&&_

Semigroup:|| : Semigroup Bool
Semigroup:|| = Semigroup: _||_

-- Bool is monoid with respect to _&&_ and _||_.

open import Data.Monoid

Monoid:&& : Monoid Bool
Monoid:&& = Monoid: {{Semigroup:&&}} true

Monoid:|| : Monoid Bool
Monoid:|| = Monoid: {{Semigroup:||}} false
