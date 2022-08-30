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
  constructor asDual
  field getDual : a

open Dual public

instance
  Semigroup-Dual : {{Semigroup a}} -> Semigroup (Dual a)
  Semigroup-Dual ._<>_ x y = asDual (getDual y <> getDual x)

  Monoid-Dual : {{Monoid a}} -> Monoid (Dual a)
  Monoid-Dual .mempty = asDual mempty

  Functor-Dual : Functor Dual
  Functor-Dual .map f = asDual <<< f <<< getDual

  Applicative-Dual : Applicative Dual
  Applicative-Dual .pure = asDual
  Applicative-Dual ._<*>_ f x = asDual $ (getDual f) (getDual x)

  Monad-Dual : Monad Dual
  Monad-Dual ._>>=_ (asDual x) k = k x

  Show-Dual : {{Show a}} -> Show (Dual a)
  Show-Dual .showsPrec prec x = showParen (prec > appPrec) $
    showString "asDual " <<< showsPrec appPrec+1 (getDual x)
