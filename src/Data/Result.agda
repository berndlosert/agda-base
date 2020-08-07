module Data.Result where

open import Prelude

private variable e : Set

data Result (e a : Set) : Set where
  Error : e -> Result e a
  Ok : a -> Result e a

instance
  FunctorResult : Functor (Result e)
  FunctorResult .map f = λ where
    (Ok x) -> Ok (f x)
    (Error e) -> Error e

  ApplicativeResult : {{_ : Semigroup e}} -> Applicative (Result e)
  ApplicativeResult .pure = Ok
  ApplicativeResult ._<*>_ = λ where
    (Ok f) (Ok x) -> Ok (f x)
    (Ok _) (Error e) -> Error e
    (Error e) (Error e') -> Error (e <> e')
    (Error e) (Ok _) -> Error e
