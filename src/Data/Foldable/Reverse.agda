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
  constructor aReverse
  field getReverse : f a

open Reverse public

instance
  Foldable-Reverse : {{Foldable f}} -> Foldable (Reverse f)
  Foldable-Reverse .foldr step init (aReverse xs) = foldl (flip step) init xs

  Functor-Reverse : {{Functor f}} -> Functor (Reverse f)
  Functor-Reverse .map f (aReverse x) = aReverse (map f x)

  Applicative-Reverse : {{Applicative f}} -> Applicative (Reverse f)
  Applicative-Reverse .pure x = aReverse (pure x)
  Applicative-Reverse ._<*>_ (aReverse f) (aReverse x) = aReverse (f <*> x)

  Monad-Reverse : {{Monad m}} -> Monad (Reverse m)
  Monad-Reverse ._>>=_ (aReverse m) k = aReverse (m >>= (k >>> getReverse))
