{-# OPTIONS --type-in-type #-}

module Data.Type where

open import Agda.Builtin.Equality public
  using (refl)
  renaming (_≡_ to _===_)

open import Agda.Builtin.TrustMe public
  renaming (primTrustMe to trustMe)

open import Data.Boolean public
open import Data.Either public
open import Data.Pair public
open import Data.Semiring public
open import Data.Unit public
open import Data.Void public

instance
  booleanSet : Boolean Set
  booleanSet .ff = Void
  booleanSet .tt = Unit
  booleanSet .not A = A -> Void
  booleanSet ._||_ = Either
  booleanSet ._&&_ = Pair

  semiringSet : Semiring Set
  semiringSet .zero = Void
  semiringSet .one = Unit
  semiringSet ._+_ = Either
  semiringSet ._*_ = Pair
