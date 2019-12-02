{-# OPTIONS --type-in-type #-}

module Control.Monad.State where

open import Control.Category
open import Control.Monad
open import Data.Functor
open import Data.Product

-- State S X models state transitions where the states are of type S and the
-- transitions produce an output of type X.
State : Set -> Set -> Set`
State S X = S -> X * S

-- The runState function carries out a state transition using the given
-- starting state.
runState : {S X : Set} -> State S X -> S -> (X * S)
runState trans s = trans s

-- The evalState function runs a state transition and returns the output.
evalState : {S X : Set} -> State S X -> S -> X
evalState trans = runState trans >>> fst

-- The execState function runs a state transition and returns the new state.
execState : {S X : Set} -> State S X -> S -> S
execState trans = runState trans >>> snd

instance
  -- State S is a functor.
  Functor:State : {S : Set} -> Endofunctor Sets (State S)
  Functor:State .map f t s = let (x , s') = t s in (f x , s')

  -- State S is also a monad. The return operation takes a value x and returns
  -- a transition that outputs x while staying in the same state. The bind
  -- operation does function application to the output all the while
  -- transitioning state.
  Monad:State : {S : Set} -> Monad Sets (State S)
  Monad:State .join t s = let (t' , s') = t s in t' s'
  Monad:State .return x s = (x , s)
