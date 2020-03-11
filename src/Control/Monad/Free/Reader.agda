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
  Functor:Reader : forall {R} -> Functor (Reader R)
  Functor:Reader .map = _<<<_

-- The function ask returns the config. value.

import Control.Monad.Eff as Eff
open Eff using (Eff)
open import Data.Functor.Union

ask : forall {R Fs} {{_ : Member (Reader R) Fs}} -> Eff Fs R
ask = Eff.send id

-- Run a Reader computation with a given config. value to get an actual value.

open import Control.Monad
open import Data.List

run : forall {R Fs X} -> R -> Eff (Reader R :: Fs) X -> Eff Fs X
run {R} {Fs} r eff = Eff.interpret t eff
  where
    t : Union (Reader R :: Fs) ~> Eff Fs
    t (left k) = return (k r)
    t (right u) = Eff.lift u

-- Reader R is a monad. The return operation creates Reader computations that
-- do not depend on config. values. The bind operation essentially passes
-- along config. values during function application.

open import Data.Function

instance
  Monad:Reader : forall {R} -> Monad Sets (Reader R)
  Monad:Reader .return x = const x
  Monad:Reader .extend f m = \ r -> f (m r) r
