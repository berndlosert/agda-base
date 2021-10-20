module Data.Monoid.Dual where

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

-------------------------------------------------------------------------------
-- Dual
-------------------------------------------------------------------------------

-- For dual semigroups, monoids, etc.
record Dual (a : Set) : Set where
  constructor aDual
  field getDual : a

open Dual public

instance
  Semigroup-Dual : {{Semigroup a}} -> Semigroup (Dual a)
  Semigroup-Dual ._<>_ x y = aDual (getDual y <> getDual x)

  Monoid-Dual : {{Monoid a}} -> Monoid (Dual a)
  Monoid-Dual .mempty = aDual mempty

  Functor-Dual : Functor Dual
  Functor-Dual .map f = aDual <<< f <<< getDual

  Applicative-Dual : Applicative Dual
  Applicative-Dual .pure = aDual
  Applicative-Dual ._<*>_ f x = aDual $ (getDual f) (getDual x)

  Monad-Dual : Monad Dual
  Monad-Dual ._>>=_ (aDual x) k = k x

  Show-Dual : {{Show a}} -> Show (Dual a)
  Show-Dual .showsPrec prec x = showParen (prec > appPrec) $
    showString "aDual " <<< showsPrec appPrec+1 (getDual x)
