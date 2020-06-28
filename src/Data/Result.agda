{-# OPTIONS --type-in-type #-}

module Data.Result where

open import Prelude

private variable e : Set

data Result (e a : Set) : Set where
  Error : e -> Result e a
  Ok : a -> Result e a

instance
  functorResult : Functor (Result e)
  functorResult .map f = λ where
    (Ok x) -> Ok (f x)
    (Error e) -> Error e

  applicativeResult : {{_ : Semigroup e}} -> Applicative (Result e)
  applicativeResult .pure = Ok
  applicativeResult ._<*>_ = λ where
    (Ok f) (Ok x) -> Ok (f x)
    (Ok _) (Error e) -> Error e
    (Error e) (Error e') -> Error (e <> e')
    (Error e) (Ok _) -> Error e
