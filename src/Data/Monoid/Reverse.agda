module Data.Monoid.Reverse where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Monoid.Dual
open import Data.Monoid.Foldable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    f m : Type -> Type

-------------------------------------------------------------------------------
-- Reverse
-------------------------------------------------------------------------------

record Reverse (f : Type -> Type) (a : Type) : Type where
  constructor reverse
  field getReverse : f a

open Reverse public

instance
  Foldable-Reverse : {{Foldable f}} -> Foldable (Reverse f)
  Foldable-Reverse .foldMap f xs = getDual (foldMap (asDual <<< f) xs)

  Functor-Reverse : {{Functor f}} -> Functor (Reverse f)
  Functor-Reverse .map f x = reverse (f <$> (getReverse x))

  Applicative-Reverse : {{Applicative f}} -> Applicative (Reverse f)
  Applicative-Reverse .pure x = reverse (pure x)
  Applicative-Reverse ._<*>_ f x = reverse (getReverse f <*> getReverse x)

  Monad-Reverse : {{Monad m}} -> Monad (Reverse m)
  Monad-Reverse ._>>=_ m k = reverse ((getReverse <<< k) =<< getReverse m)
