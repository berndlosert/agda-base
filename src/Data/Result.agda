{-# OPTIONS --type-in-type #-}

module Data.Result where

open import Prelude

private variable e : Set

data Result (e a : Set) : Set where
  Error : e -> Result e a
  Ok : a -> Result e a

instance
  Functor-Result : Functor (Result e)
  Functor-Result .map f = \ where
    (Ok x) -> Ok (f x)
    (Error e) -> Error e

  Applicative-Result : {{_ : Semigroup e}} -> Applicative (Result e)
  Applicative-Result .pure = Ok
  Applicative-Result ._<*>_ = \ where
    (Ok f) (Ok x) -> Ok (f x)
    (Ok _) (Error e) -> Error e
    (Error e) (Error e') -> Error (e <> e')
    (Error e) (Ok _) -> Error e
