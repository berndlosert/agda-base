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
  HasAdd-Ap : {{Applicative f}} -> {{HasAdd a}} -> HasAdd (Ap f a)
  HasAdd-Ap ._+_ x y = asAp (| getAp x + getAp y |)

  HasMul-Ap : {{Applicative f}} -> {{HasMul a}} -> HasMul (Ap f a)
  HasMul-Ap ._*_ x y = asAp (| getAp x * getAp y |)

  HasNeg-Ap : {{Applicative f}} -> {{HasNeg a}} -> HasNeg (Ap f a)
  HasNeg-Ap .-_ x = asAp (| - getAp x |)

  Semigroup-Ap : {{Applicative f}} -> {{Semigroup a}} -> Semigroup (Ap f a)
  Semigroup-Ap ._<>_ x y = asAp (| getAp x <> getAp y |)

  Monoid-Ap : {{Applicative f}} -> {{Monoid a}} -> Monoid (Ap f a)
  Monoid-Ap .mempty = asAp (pure mempty)
