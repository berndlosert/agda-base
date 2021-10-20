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
    a : Set

-------------------------------------------------------------------------------
-- Identity
-------------------------------------------------------------------------------

record Identity (a : Set) : Set where
  constructor anIdentity
  field runIdentity : a

open Identity public

instance
  Eq-Identity : {{Eq a}} -> Eq (Identity a)
  Eq-Identity ._==_ = _==_ on runIdentity

  Ord-Identity : {{Ord a}} -> Ord (Identity a)
  Ord-Identity ._<_ = _<_ on runIdentity

  Semigroup-Identity : {{Semigroup a}} -> Semigroup (Identity a)
  Semigroup-Identity ._<>_ x y = anIdentity (runIdentity x <> runIdentity y)

  Monoid-Identity : {{Monoid a}} -> Monoid (Identity a)
  Monoid-Identity .mempty = anIdentity mempty

  Foldable-Identity : Foldable Identity
  Foldable-Identity .foldr step init x = step (runIdentity x) init

  Functor-Identity : Functor Identity
  Functor-Identity .map f = anIdentity <<< f <<< runIdentity

  Applicative-Identity : Applicative Identity
  Applicative-Identity .pure = anIdentity
  Applicative-Identity ._<*>_ = map <<< runIdentity

  Monad-Identity : Monad Identity
  Monad-Identity ._>>=_ x k = k (runIdentity x)

  Show-Identity : {{Show a}} -> Show (Identity a)
  Show-Identity .showsPrec prec x = showParen (prec > appPrec)
    (showString "anIdentity " <<< showsPrec appPrec+1 (runIdentity x))
