{-# OPTIONS --type-in-type #-}

module Control.Monad.Reader where

-- Reader R X models computations of type X that depend on a config. value of
-- type R. Such computations are called Reader computations.

Reader : Set -> Set -> Set
Reader R X = R -> X

-- Reader R is a functor.

open import Data.Functor

instance
  Functor:Reader : forall {R} -> Endofunctor Sets (Reader R)
  Functor:Reader .map f r = r >>> f

-- Reader R is a monad.

open import Control.Monad

instance
  Monad:Reader : forall {R} -> Monad Sets (Reader R)
  Monad:Reader .return x = \ _ -> x
  Monad:Reader .extend f m = \ r -> f (m r) r

module Reader where

  -- The function ask returns the config. value.

  ask : forall {R} -> Reader R R
  ask = id

  -- Run a Reader computation with a given config. value to get an actual value.

  open import Data.List

  run : forall {R X} -> Reader R X -> R -> X
  run = id
