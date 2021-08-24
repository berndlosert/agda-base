{-# OPTIONS --type-in-type #-}

module Data.Functor.Identity where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Type

-------------------------------------------------------------------------------
-- Identity
-------------------------------------------------------------------------------

record Identity (a : Type) : Type where
  constructor Identity:
  field runIdentity : a

open Identity public

instance
  Eq-Identity : {{Eq a}} -> Eq (Identity a)
  Eq-Identity ._==_ = _==_ on runIdentity

  Ord-Identity : {{Ord a}} -> Ord (Identity a)
  Ord-Identity .compare = compare on runIdentity

  Semigroup-Identity : {{Semigroup a}} -> Semigroup (Identity a)
  Semigroup-Identity ._<>_ x y = Identity: <<< _<>_ on runIdentity

  Monoid-Identity : {{Monoid a}} -> Monoid (Identity a)
  Monoid-Identity .neutral = Identity: neutral

  Foldable-Identity : Foldable Identity
  Foldable-Identity .foldr f z x = f (runIdentity x) z

  Functor-Identity : Functor Identity
  Functor-Identity .map f = Identity: <<< f <<< runIdentity

  Applicative-Identity : Applicative Identity
  Applicative-Identity .pure = Identity:
  Applicative-Identity ._<*>_ = map <<< runIdentity

  Monad-Identity : Monad Identity
  Monad-Identity ._>>=_ x k = k (runIdentity x)

  Show-Identity : {{Show a}} -> Show (Identity a)
  Show-Identity .showsPrec d x = showParen (d > appPrec)
    (showString "Identity: " <<< showsPrec appPrec+1 (runIdentity x))
