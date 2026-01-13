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
    a : Type
    f : Type -> Type

-------------------------------------------------------------------------------
-- Ap
-------------------------------------------------------------------------------

record Ap (f : Type -> Type) (a : Type) : Type where
  constructor asAp
  field getAp : f a

open Ap public

instance
  Addable-Ap : {{Applicative f}} -> {{Addable a}} -> Addable (Ap f a)
  Addable-Ap ._+_ x y = asAp (| getAp x + getAp y |)

  Multiplicable-Ap : {{Applicative f}} -> {{Multiplicable a}} -> Multiplicable (Ap f a)
  Multiplicable-Ap ._*_ x y = asAp (| getAp x * getAp y |)

  Negatable-Ap : {{Applicative f}} -> {{Negatable a}} -> Negatable (Ap f a)
  Negatable-Ap .-_ x = asAp (| - getAp x |)

  Subtractable-Ap : {{Applicative f}} -> {{Subtractable a}} -> Subtractable (Ap f a)
  Subtractable-Ap ._-_ x y = asAp (| getAp x - getAp y |)

  Exponentiable-Ap : {{Applicative f}} -> {{Exponentiable a}} -> Exponentiable (Ap f a)
  Exponentiable-Ap {{_}} {{inst}} .Power = Power {{inst}}
  Exponentiable-Ap ._^_ x n = asAp (| getAp x ^ (pure n) |)

  Semigroup-Ap : {{Applicative f}} -> {{Semigroup a}} -> Semigroup (Ap f a)
  Semigroup-Ap ._<>_ x y = asAp (| getAp x <> getAp y |)

  Monoid-Ap : {{Applicative f}} -> {{Monoid a}} -> Monoid (Ap f a)
  Monoid-Ap .mempty = asAp (pure mempty)
