{-# OPTIONS --type-in-type #-}

module Control.Monad.Reader where

open import Prelude

-- Reader R X models computations of type X that depend on a config. value of
-- type R. Such computations are called Reader computations.
Reader : Set -> Set -> Set
Reader R X = R -> X

-- Reader R is a functor.
instance
  Functor:Reader : forall {R} -> Functor (Reader R)
  Functor:Reader .map f r = r >>> f

-- Reader R is a monad.
instance
  Monad:Reader : forall {R} -> Monad (Reader R)
  Monad:Reader .return x = \ _ -> x
  Monad:Reader .extend f m = \ r -> f (m r) r

-- The function ask returns the config. value.
ask : forall {R} -> Reader R R
ask = id

-- Run a Reader computation with a given config. value to get an actual value.
run : forall {R X} -> Reader R X -> R -> X
run = id
