{-# OPTIONS --type-in-type #-}

module Control.Monad.Reader where

-- Reader R X models computations of type X that depend on a config. value of
-- type R. Such computations are called Reader computations.

Reader : Set -> Set -> Set
Reader R X = R -> X

-- Reader R is a functor whose map is just function composition.

open import Control.Category
open import Data.Functor

instance
  Functor:Reader : forall {R} -> Endofunctor Sets (Reader R)
  Functor:Reader .map = _<<<_

-- The function ask returns the config. value.

open import Control.Monad.Eff

ask : forall {R Fs} {{_ : Member (Reader R) Fs}} -> Eff Fs R 
ask = liftEff id

-- Run a Reader computation with a given config. value to get an actual value.

open import Control.Monad

runReader : forall {R Fs X} -> Eff (Reader R :: Fs) X -> R -> Eff Fs X
runReader eff r = Eff: \ t -> runEff eff \ where 
  (left reader) -> return (reader r)
  (right u) -> t u

-- Reader R is a monad. The return operation creates Reader computations that
-- do not depend on config. values. The bind operation essentially passes
-- along config. values during function application.

open import Data.Function

instance
  Monad:Reader : forall {R} -> Monad Sets (Reader R)
  Monad:Reader .join f r = f r r
  Monad:Reader .return x = const x
