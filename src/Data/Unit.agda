{-# OPTIONS --type-in-type #-}

module Data.Unit where

-- An empty record type is a record type with no fields. Unit is the "official"
-- empty record type whose constructor is named tt (trivially true). It is the
-- terminal object (up to isomorphism) in the category Sets.

open import Agda.Builtin.Unit public
  renaming (⊤ to Unit)

-- The trivial function is evidence that Unit satisfies the universal property
-- of terminal objects in the category Sets. You can also think of it as the
-- unfold operation for Unit.

trivial : {X : Set} -> X -> Unit
trivial _ = tt

-- A thunk is a value wrapped inside a function that takes "no arguments".
-- Another way to think about thunk is as the fold operation for Unit
-- (considered as a type with one constructor).

thunk : {X : Set} -> X -> Unit -> X
thunk x tt = x

-- The inverse of thunk is unthunk. Together, these two functions witness an
-- isomorphism between Unit -> X and X. They also prove that the identity
-- functor id {{Sets}} is representable by Unit.

unthunk : {X : Set} -> (Unit -> X) -> X
unthunk x = x tt

-- Unit forms a one-element semigroup.

open import Data.Semigroup

instance
  Semigroup:Unit : Semigroup Unit
  Semigroup:Unit = Semigroup: \ _ _ -> tt

-- Unit forms a one-element monoid.

open import Data.Monoid

instance
  Monoid:Unit : Monoid Unit
  Monoid:Unit = Monoid: tt
