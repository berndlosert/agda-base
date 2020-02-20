{-# OPTIONS --type-in-type #-}

module Data.Maybe.Base where

-- Maybe X is used for representing optional values of X by adding an extra
-- nothing value to X.

data Maybe (X : Set) : Set where
  nothing : Maybe X
  just : X -> Maybe X

-- This tells the Agda compiler to compile Maybe above to Haskell's Maybe.

{-# COMPILE GHC Maybe = data Maybe (Nothing | Just) #-}

-- Maybe forms a functor.

open import Data.Functor public

instance
  Functor:Maybe : Endofunctor Sets Maybe
  Functor:Maybe .map f nothing = nothing
  Functor:Maybe .map f (just x) = just (f x)

-- Maybe forms a monad, which we can use to model computations that can fail.

open import Control.Category
open import Control.Monad public

instance
  Monad:Maybe : Monad Sets Maybe
  Monad:Maybe .return = just
  Monad:Maybe .extend k nothing = nothing
  Monad:Maybe .extend k (just x) = k x

-- We derive the Applicative instance of Maybe from the Monad instance.

open import Control.Applicative public

instance
  Applicative:Maybe : Applicative Maybe
  Applicative:Maybe = Applicative: ap return

-- Maybe is an alternative functor.

open import Control.Alternative public

instance
  Alternative:Maybe : Alternative Maybe
  Alternative:Maybe ._<|>_ nothing nothing = nothing
  Alternative:Maybe ._<|>_ (just x) nothing = just x
  Alternative:Maybe ._<|>_ nothing (just x) = just x
  Alternative:Maybe ._<|>_ (just x) (just y) = just x
  Alternative:Maybe .empty = nothing

-- This is the left-biased Semigroup instance of Maybe X. This is useful when
-- you have a list of Maybe X values and you want to pick the first one that is
-- not nothing.

open import Data.Semigroup

instance
  Semigroup:First : forall {X} -> Semigroup (Maybe X)
  Semigroup:First = Semigroup: \ where
    nothing _ -> nothing
    (just x) _ -> just x
