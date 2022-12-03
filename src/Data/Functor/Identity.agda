module Data.Functor.Identity where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Comonad
open import Data.Foldable
open import Data.String.Show

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set

-------------------------------------------------------------------------------
-- Identity
-------------------------------------------------------------------------------

record Identity (a : Set) : Set where
  constructor asIdentity
  field runIdentity : a

open Identity public

instance
  Coercible-from-Identity : Coercible (Identity a) a
  Coercible-from-Identity = coercible

  Coercible-to-Identity : Coercible a (Identity a)
  Coercible-to-Identity = coercible

  Eq-Identity : {{Eq a}} -> Eq (Identity a)
  Eq-Identity {a} ._==_ = coerce (id {a -> a -> Bool} _==_)

  Ord-Identity : {{Ord a}} -> Ord (Identity a)
  Ord-Identity {a} ._<_ = coerce (id {a -> a -> Bool} _<_)

  Semigroup-Identity : {{Semigroup a}} -> Semigroup (Identity a)
  Semigroup-Identity {a} ._<>_ = coerce (id {a -> a -> a} _<>_)

  Monoid-Identity : {{Monoid a}} -> Monoid (Identity a)
  Monoid-Identity .mempty = asIdentity mempty

  Foldable-Identity : Foldable Identity
  Foldable-Identity .foldr step init x = step (runIdentity x) init

  Functor-Identity : Functor Identity
  Functor-Identity .map = coerce

  Applicative-Identity : Applicative Identity
  Applicative-Identity .pure = asIdentity
  Applicative-Identity ._<*>_ = coerce

  Monad-Identity : Monad Identity
  Monad-Identity ._>>=_ x k = k (runIdentity x)

  Comonad-Identity : Comonad Identity
  Comonad-Identity .extract = runIdentity
  Comonad-Identity .extend f x = asIdentity (f x)

  Show-Identity : {{Show a}} -> Show (Identity a)
  Show-Identity .show = showDefault
  Show-Identity .showsPrec prec (asIdentity x) =
    showsUnaryWith showsPrec "asIdentity" prec x
