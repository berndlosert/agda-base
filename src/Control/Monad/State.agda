{-# OPTIONS --type-in-type #-}

module Control.Monad.State where

open import Prelude

-- State S X models state transitions where the states are of type S and the
-- transitions produce an output of type X.
State : Set -> Set -> Set
State S X = S -> X * S

-- State S forms a functor.
open import Data.Pair

instance
  Functor:State : forall {S} -> Endofunctor Sets (State S)
  Functor:State .map f m = \ s -> cross f id (m s)

-- State S forms a monad.
instance
  Monad:State : forall {S} -> Monad Sets (State S)
  Monad:State .return x s = Pair: x s
  Monad:State .extend f m = \ s -> let (Pair: x s') = m s in (f x) s'

-- Applicative instance of State S derived from the monad instance.
instance
  Applicative:State : forall {S} -> Applicative (State S)
  Applicative:State = Applicative: ap return

run : forall {S X} -> State S X -> S -> (X * S)
run = id

-- The eval function runs a state transition and returns the output.
eval : {S X : Set} -> State S X -> S -> X
eval trans = run trans >>> fst

-- The exec function runs a state transition and returns the new state.
exec : forall {S X} -> State S X -> S -> S
exec trans = run trans >>> snd
