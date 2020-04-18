{-# OPTIONS --type-in-type #-}

module Data.Functor.Id where

open import Prelude

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
