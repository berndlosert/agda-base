{-# OPTIONS --type-in-type #-}

module Data.Maybe where

open import Data.Maybe.Base public
  hiding (module Maybe)

module Maybe where

  -- Maybe forms a functor.
  
  open import Control.Category
  open import Data.Functor
  
  -- Maybe forms a monad, which we can use to model computations that can fail.
  
  open import Control.Monad
  
  instance
    Monad:Maybe : Monad Sets Maybe
    Monad:Maybe .return = just
    Monad:Maybe .extend k nothing = nothing
    Monad:Maybe .extend k (just x) = k x
  
  -- We derive the Functor instance of Maybe from the Monad instance.

  instance
    Functor:Maybe : Endofunctor Sets Maybe
    Functor:Maybe = Functor: liftM

  -- We derive the Applicative instance of Maybe from the Monad instance.
  
  open import Control.Applicative
  
  instance
    Applicative:Maybe : Applicative Maybe
    Applicative:Maybe = Idiom: ap return

  -- This is the left-biased Semigroup instance of Maybe X. This is useful when
  -- you have a list of Maybe X values and you want to pick the first one that is
  -- not nothing.
  
  open import Data.Semigroup
  
  instance
    Semigroup:First : forall {X} -> Semigroup (Maybe X)
    Semigroup:First = Semigroup: \ where
      nothing _ -> nothing
      (just x) _ -> just x

  -- The from function takes a default value and and Maybe value. If the Maybe
  -- is nothing, it returns the default values; otherwise, it returns the value
  -- contained in the Maybe.

  from : forall {X} -> X -> Maybe X -> X 
  from x nothing = x 
  from _ (just x) = x

open Maybe public
  using (
    Monad:Maybe;
    Functor:Maybe;
    Applicative:Maybe;
    Semigroup:First
  )
