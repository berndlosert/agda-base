{-# OPTIONS --type-in-type #-}

module Data.Functor.Id where

open import Control.Applicative using (Applicative)
open import Control.Applicative public using (_<*>_; pure)
open import Control.Monad using (Monad)
open import Control.Monad public using (_>>=_; return)
open import Data.Eq using (Eq)
open import Data.Eq public using (_==_; _/=_)
open import Data.Function using (_<<<_)
open import Data.Functor using (Functor)
open import Data.Functor public using (map)
open import Data.Monoid using (Monoid; mempty)
open import Data.Ord using (Ord; _<_)
open import Data.Semigroup using (Semigroup; _<>_)

private variable A : Set

record Id (A : Set) : Set where
  constructor toId
  field fromId : A

open Id public

instance
  functorId : Functor Id
  functorId .map f = toId <<< f <<< fromId

  applicativeId : Applicative Id
  applicativeId .pure = toId
  applicativeId ._<*>_ = map <<< fromId

  monadId : Monad Id
  monadId ._>>=_ a k = k (fromId a)

  eqId : {{_ : Eq A}} -> Eq (Id A)
  eqId ._==_ x y = fromId (| _==_ x y |)

  ordId : {{_ : Ord A}} -> Ord (Id A)
  ordId ._<_ x y = fromId (| _<_ x y |)

  semigroupId : {{_ : Semigroup A}} -> Semigroup (Id A)
  semigroupId ._<>_ x y = (| _<>_ x y |)

  monoidId : {{_ : Monoid A}} -> Monoid (Id A)
  monoidId .mempty = toId mempty
