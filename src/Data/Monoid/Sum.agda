module Data.Monoid.Sum where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.String.Show

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Type

-------------------------------------------------------------------------------
-- Literals
-------------------------------------------------------------------------------

instance
  _ = FromNat-Int
  _ = FromNat-Float

-------------------------------------------------------------------------------
-- Sum
-------------------------------------------------------------------------------

-- For additive semigroups, monoids, etc.
abstract
  Sum : Type -> Type
  Sum a = a

  getSum : Sum a -> a
  getSum x = x

asSum : {{Addable a}} -> a -> Sum a
asSum x = x

record Sum (a : Type) {{Addable a}} : Type where
  constructor asSum
  field getSum : a

open Sum public

module _ {a : Type} {{Addable a}} where
  instance
    Semigroup-Eq : {{Eq a}} -> Eq (Sum a)
    Semigroup-Eq ._==_ x y = getSum x == getSum y

instance
  Semigroup-Sum-Nat : Semigroup (Sum Nat)
  Semigroup-Sum-Nat ._<>_ x y = asSum (getSum x + getSum y)

  Monoid-Sum-Nat : Monoid (Sum Nat)
  Monoid-Sum-Nat .mempty = asSum 0

  Semigroup-Sum-Nat1 : Semigroup (Sum Nat1)
  Semigroup-Sum-Nat1 ._<>_ (asSum m) (asSum n) = asSum (m + n)

  Semigroup-Sum-Int : Semigroup (Sum Int)
  Semigroup-Sum-Int ._<>_ x y = asSum (getSum x + getSum y)

  Monoid-Sum-Int : Monoid (Sum Int)
  Monoid-Sum-Int .mempty = asSum 0

  Semigroup-Sum-Float : Semigroup (Sum Float)
  Semigroup-Sum-Float ._<>_ x y = asSum (getSum x + getSum y)

  Monoid-Sum-Float : Monoid (Sum Float)
  Monoid-Sum-Float .mempty = asSum 0

  Functor-Sum : Functor Sum
  Functor-Sum .map f x = asSum (f (getSum x))

  Applicative-Sum : Applicative Sum
  Applicative-Sum .pure = asSum
  Applicative-Sum ._<*>_ f x = asSum (getSum f (getSum x))

  Monad-Sum : Monad Sum
  Monad-Sum ._>>=_ (asSum x) k = k x

  Show-Sum : {{Show a}} -> Show (Sum a)
  Show-Sum .show = showDefault
  Show-Sum .showsPrec prec (asSum x) =
    showsUnaryWith showsPrec "asSum" prec x

-------------------------------------------------------------------------------
-- Rewrite rules
-------------------------------------------------------------------------------

sumNatRewrite : (m n : Nat) -> getSum (asSum m <> asSum n) === m + n
sumNatRewrite m n = refl