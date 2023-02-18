module Data.Functor.Product where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable
open import Data.Functor.Contravariant
open import Data.String.Show
open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set
    f g : Set -> Set

-------------------------------------------------------------------------------
-- Product
-------------------------------------------------------------------------------

record Product {k : Set} (f g : k -> Set) (a : k) : Set where
  constructor pair
  field
    fstP : f a
    sndP : g a

open Product public

instance
  Functor-Product : {{Functor f}} -> {{Functor g}} -> Functor (Product f g)
  Functor-Product .map f (pair x y) = pair (map f x) (map f y)

  Contravariant-Product : {{Contravariant f}} -> {{Contravariant g}} -> Contravariant (Product f g)
  Contravariant-Product .cmap f (pair x y) = pair (cmap f x) (cmap f y)

  Applicative-Product : {{Applicative f}} -> {{Applicative g}} -> Applicative (Product f g)
  Applicative-Product .pure x = pair (pure x) (pure x)
  Applicative-Product ._<*>_ (pair f g) (pair x y) = pair (f <*> x) (g <*> y)

  Monad-Product : {{Monad f}} -> {{Monad g}} -> Monad (Product f g)
  Monad-Product ._>>=_ (pair x y) k = pair (x >>= k >>> fstP) (y >>= k >>> sndP)

  Foldable-Product : {{Foldable f}} -> {{Foldable g}} -> Foldable (Product f g)
  Foldable-Product .foldr step init (pair x y) = foldr step (foldr step init x) y

  Traversable-Product : {{Traversable f}} -> {{Traversable g}} -> Traversable (Product f g)
  Traversable-Product .traverse f (pair x y) = (| pair (traverse f x) (traverse f y) |)

  Show-Product : {{Show (f a)}} -> {{Show (g a)}} -> Show (Product f g a)
  Show-Product .show = showDefault
  Show-Product .showsPrec prec (pair x y) = showsBinaryWith showsPrec showsPrec "pair" prec x y
