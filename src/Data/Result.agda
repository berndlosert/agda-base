{-# OPTIONS --type-in-type #-}

module Data.Result where

open import Prelude

data Result (E X : Set) : Set where
  error : E -> Result E X
  ok : X -> Result E X

instance
  functorResult : forall {E} -> Functor (Result E)
  functorResult .map f = \ where
    (ok x) -> ok (f x)
    (error e) -> error e

  applicativeResult : forall {E} {{_ : Semigroup E}}
    -> Applicative (Result E)
  applicativeResult .pure = ok
  applicativeResult ._<*>_ = \ where
    (ok f) (ok x) -> ok (f x)
    (ok _) (error e) -> error e
    (error e) (error e') -> error (e <> e')
    (error e) (ok _) -> error e
