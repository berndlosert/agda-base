{-# OPTIONS --type-in-type #-}

module Control.Monad.Reader where

open import Control.Category
open import Control.Monad
open import Data.Function
open import Data.Functor

-- Reader R X models computations of type X that depend on a config. value of
-- type R. Such computations are called Reader computations.
Reader : Set -> Sets => Sets
Reader R X = R -> X

-- Run a Reader computation with a given config. value to get an actual value.
runReader : {R X : Set} -> Reader R X -> R -> X
runReader x r = x r

-- The withReader function allows us to modify the type of the config. value
-- of Reader computations.
withReader : {R R' X : Set} -> (R -> R') -> Reader R' X -> Reader R X
withReader modify x r = runReader x (modify r)

instance
  -- Reader R is a functor whose map is just function composition.
  Functor:Reader : {R : Set} -> Endofunctor Sets (Reader R)
  Functor:Reader .map = _<<<_
  
  -- Reader R is a monad. The return operation creates Reader computations that
  -- do not depend on config. values. The bind operation essentially passes
  -- along config. values during function application.
  Monad:Reader : {R : Set} -> Monad Sets (Reader R)
  Monad:Reader .join f r = f r r
  Monad:Reader .return x = const x

-- The function ask returns the config. value.
ask : {R : Set} -> Reader R R
ask = id
