{-# OPTIONS --type-in-type #-}

module Data.List1.Base where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import String.Show

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Type

-------------------------------------------------------------------------------
-- List1
-------------------------------------------------------------------------------

infixr 5 _:|_
data List1 (a : Type) : Type where
  _:|_ : a -> List a -> List1 a

instance
  Eq-List1 : {{Eq a}} -> Eq (List1 a)
  Eq-List1 ._==_ (x :| xs) (y :| ys) = x == y && xs == ys

  Ord-List1 : {{Ord a}} -> Ord (List1 a)
  Ord-List1 .compare (x :| xs) (y :| ys) =
    case compare x y of \ where
      LT -> LT
      GT -> GT
      EQ -> compare xs ys

  Semigroup-List1 : Semigroup (List1 a)
  Semigroup-List1 ._<>_ (x :| xs) (y :| ys) = x :| xs <> (y :: []) <> ys

  Functor-List1 : Functor List1
  Functor-List1 .map f (x :| xs) = f x :| map f xs

  Applicative-List1 : Applicative List1
  Applicative-List1 .pure = _:| []
  Applicative-List1 ._<*>_ (f :| fs) (x :| xs) = f x :| (fs <*> xs)

  Monad-List1 : Monad List1
  Monad-List1 ._>>=_ (x :| xs) k = case k x of \ where
    (y :| ys) -> y :| (ys <> (xs >>= k >>> \ where (z :| zs) -> z :: zs))

  Show-List1 : {{Show a}} -> Show (List1 a)
  Show-List1 .showsPrec d (x :| xs) = showsPrec d (x :: xs)
