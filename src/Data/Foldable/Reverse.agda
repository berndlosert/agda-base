{-# OPTIONS --type-in-type #-}

module Data.Foldable.Reverse where

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
    f m : Set -> Set

-------------------------------------------------------------------------------
-- Reverse
-------------------------------------------------------------------------------

record Reverse (f : Set -> Set) (a : Set) : Set where
  constructor toReverse
  field getReverse : f a

open Reverse public

instance
  Foldable-Reverse : {{Foldable f}} -> Foldable (Reverse f)
  Foldable-Reverse .foldr step init (toReverse xs) = foldl (flip step) init xs

  Functor-Reverse : {{Functor f}} -> Functor (Reverse f)
  Functor-Reverse .map f (toReverse x) = toReverse (map f x)

  Applicative-Reverse : {{Applicative f}} -> Applicative (Reverse f)
  Applicative-Reverse .pure x = toReverse (pure x)
  Applicative-Reverse ._<*>_ (toReverse f) (toReverse x) = toReverse (f <*> x)

  Monad-Reverse : {{Monad m}} -> Monad (Reverse m)
  Monad-Reverse ._>>=_ (toReverse m) k = toReverse (m >>= (k >>> getReverse))
