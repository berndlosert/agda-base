{-# OPTIONS --type-in-type #-}

module Control.Monad.Reader where

-- Reader R X models computations of type X that depend on a config. value of
-- type R. Such computations are called Reader computations.

Reader : Set -> Set -> Set
Reader R X = R -> X

-- Run a Reader computation with a given config. value to get an actual value.

runReader : forall {R X} -> Reader R X -> R -> X
runReader x r = x r

-- The withReader function allows us to modify the type of the config. value
-- of Reader computations.

withReader : forall {R R' X} -> (R -> R') -> Reader R' X -> Reader R X
withReader modify x r = runReader x (modify r)

-- Reader R is a functor whose map is just function composition.

open import Control.Category
open import Data.Functor

instance
  Functor:Reader : forall {R} -> Endofunctor Sets (Reader R)
  Functor:Reader .map = _<<<_

-- Reader R is a monad. The return operation creates Reader computations that
-- do not depend on config. values. The bind operation essentially passes
-- along config. values during function application.

open import Control.Monad
open import Data.Function

instance
  Monad:Reader : forall {R} -> Monad Sets (Reader R)
  Monad:Reader .join f r = f r r
  Monad:Reader .return x = const x

-- The function ask returns the config. value.

ask : {R : Set} -> Reader R R
ask = id
