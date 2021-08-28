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
  constructor Reverse:
  field getReverse : f a

open Reverse public

instance
  Foldable-Reverse : {{Foldable f}} -> Foldable (Reverse f)
  Foldable-Reverse .foldr f z (Reverse: xs) = foldl (flip f) z xs

  Functor-Reverse : {{Functor f}} -> Functor (Reverse f)
  Functor-Reverse .map f (Reverse: x) = Reverse: (map f x)

  Applicative-Reverse : {{Applicative f}} -> Applicative (Reverse f)
  Applicative-Reverse .pure x = Reverse: (pure x)
  Applicative-Reverse ._<*>_ (Reverse: f) (Reverse: x) = Reverse: (f <*> x)

  Monad-Reverse : {{Monad m}} -> Monad (Reverse m)
  Monad-Reverse ._>>=_ (Reverse: m) k = Reverse: (m >>= (k >>> getReverse))
