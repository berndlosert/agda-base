{-# OPTIONS --type-in-type #-}

module Data.Function where

-- Export function composition (and it variants) and id from the category Sets.

open import Control.Category public
  using (
    _<<<_;
    _>>>_;
    id;
    Sets
  )

-- The flip function is proof that X -> Y -> Z and Y -> X -> Z are isomorphic.
-- If we think of -> as exponentiation, then flip is proof that exponents in
-- the cateogry Sets commute (modulo isomorphism).

private
  variable
    X : Set
    Y : Set
    Z : Set

flip : (X -> Y -> Z) -> Y -> X -> Z
flip f y x = f x y

-- This is a binary operator for effecting function application. It is the
-- curried version of apply.

infixr 0 _$_

_$_ : (X -> Y) -> X -> Y
f $ x = f x

-- This is the strict version of _$_ so that f $! x will evaluate x first
-- before applying f to it.

open import Agda.Builtin.Strict

infixr 0 _$!_

_$!_ : (X -> Y) -> X -> Y
f $! x = primForce x f

-- This is just the flipped version of _$_.

infixl 1 _&_

_&_ : X -> (X -> Y) -> Y
x & f = f x

-- The case "statement" is useful for applying pattern-matching lambdas to
-- values in a more natural way.

case_of_ = _&_

-- The const operation is used for producing constant functions. It is proof
-- that every nonempty type is weakly terminal in the category Sets.

const : X -> Y -> X
const x _ = x
