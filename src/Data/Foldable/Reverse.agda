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
  constructor asReverse
  field getReverse : f a

open Reverse public

instance
  Foldable-Reverse : {{Foldable f}} -> Foldable (Reverse f)
  Foldable-Reverse .foldr step init (asReverse xs) = foldl (flip step) init xs

  Functor-Reverse : {{Functor f}} -> Functor (Reverse f)
  Functor-Reverse .map f (asReverse x) = asReverse (map f x)

  Applicative-Reverse : {{Applicative f}} -> Applicative (Reverse f)
  Applicative-Reverse .pure x = asReverse (pure x)
  Applicative-Reverse ._<*>_ (asReverse f) (asReverse x) = asReverse (f <*> x)

  Monad-Reverse : {{Monad m}} -> Monad (Reverse m)
  Monad-Reverse ._>>=_ (asReverse m) k = asReverse (m >>= (k >>> getReverse))
