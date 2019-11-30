**********
Data.Maybe
**********
::

  {-# OPTIONS --type-in-type #-}

  module Data.Maybe where

``Maybe X`` is used for representing optional values of ``X``. It adds an extra
``nothing`` value to any set::

  data Maybe (X : Set) : Set where
    nothing : Maybe X
    just : X -> Maybe X

This tells the Agda compiler to compile ``Maybe`` above to Haskell's ``Maybe``::

  {-# COMPILE GHC Maybe = data Maybe (Nothing | Just) #-}

``Maybe`` forms a functor::

  open import Control.Category
  open import Data.Functor

  instance
    Functor:Maybe : Endofunctor Sets Maybe
    Functor:Maybe .map f nothing = nothing
    Functor:Maybe .map f (just x) = just (f x)

``Maybe`` also forms a monad, which we can use to model computations that can fail::

  open import Control.Monad

  instance
    Monad:Maybe : Monad Sets Maybe
    Monad:Maybe .join nothing = nothing
    Monad:Maybe .join (just x) = x
    Monad:Maybe .return = just

We derive the ``Applicative`` instance of ``Maybe`` from the ``Monad`` instance::

  open import Control.Applicative

  instance
    Applicative:Maybe : Applicative Maybe
    Applicative:Maybe = Idiom: ap return

This is the left-biased semigroup instance of ``Maybe X``. This is useful when
you have a list of ``Maybe X`` values and you want to pick the first one that
is not ``nothing``::

  open import Data.Semigroup

  instance
    Semigroup:First : {X : Set} -> Semigroup (Maybe X)
    Semigroup:First = Semigroup: \ where
      nothing _ -> nothing
      (just x) _ -> just x
