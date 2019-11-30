{-# OPTIONS --type-in-type #-}

module Data.Maybe where

-- Maybe X is used for representing optional values of X. Maybe is the
-- type-level version of the successor function, i.e. it adds an extra
-- nothing value to any type.
data Maybe (X : Set) : Set where
  nothing : Maybe X
  just : X -> Maybe X

{-# COMPILE GHC Maybe = data Maybe (Nothing | Just) #-}

instance
  -- Maybe is a functor.
  open import Control.Category
  open import Data.Functor
  Functor:Maybe : Endofunctor Sets Maybe
  Functor:Maybe .map f nothing = nothing
  Functor:Maybe .map f (just x) = just (f x)

  -- Maybe is a monad.
  open import Control.Monad
  Monad:Maybe : Monad Sets Maybe
  Monad:Maybe .join nothing = nothing
  Monad:Maybe .join (just x) = x
  Monad:Maybe .return = just

  -- Maybe is an applicative.
  open import Control.Applicative
  Applicative:Maybe : Applicative Maybe
  Applicative:Maybe = Idiom: ap return

  -- The left-biased semigroup instance of Maybe X.
  open import Data.Semigroup
  Semigroup:First : {X : Set} -> Semigroup (Maybe X)
  Semigroup:First = Semigroup: \ where
    nothing _ -> nothing
    (just x) _ -> just x
