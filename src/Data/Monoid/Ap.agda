module Data.Monoid.Ap where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set
    f : Set -> Set

-------------------------------------------------------------------------------
-- Ap
-------------------------------------------------------------------------------

record Ap (f : Set -> Set) (a : Set) : Set where
  constructor asAp
  field getAp : f a

open Ap public

instance
  FromNat-Ap : {{Applicative f}} -> {{FromNat a}} -> FromNat (Ap f a)
  FromNat-Ap .fromNat n = asAp (pure (fromNat n))

  Num-Ap : {{Applicative f}} -> {{Num a}} -> Num (Ap f a)
  Num-Ap ._+_ x y = asAp (| getAp x + getAp y |)
  Num-Ap ._-_ x y = asAp (| getAp x - getAp y |)
  Num-Ap .-_ x = asAp (| - getAp x |)
  Num-Ap ._*_ x y = asAp (| getAp x * getAp y |)
  Num-Ap ._^_ x n = asAp (| getAp x ^ (pure n) |)

  Semigroup-Ap : {{Applicative f}} -> {{Semigroup a}} -> Semigroup (Ap f a)
  Semigroup-Ap ._<>_ x y = asAp (| getAp x <> getAp y |)

  Monoid-Ap : {{Applicative f}} -> {{Monoid a}} -> Monoid (Ap f a)
  Monoid-Ap .mempty = asAp (pure mempty)
