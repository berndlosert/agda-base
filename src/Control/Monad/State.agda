{-# OPTIONS --type-in-type #-}

module Control.Monad.State where

-- State S X models state transitions where the states are of type S and the
-- transitions produce an output of type X.

open import Data.Product

State : Set -> Set -> Set
State S X = S -> X * S

module State where

  -- The run function carries out a state transition using the given starting
  -- state.
  
  open import Data.Function
  
  run : forall {S X} -> State S X -> S -> (X * S)
  run = id 
  
  -- The eval function runs a state transition and returns the output.
  
  eval : {S X : Set} -> State S X -> S -> X
  eval trans = run trans >>> fst
  
  -- The exec function runs a state transition and returns the new state.
  
  exec : forall {S X} -> State S X -> S -> S
  exec trans = run trans >>> snd
  
  -- State S is also a monad. The return operation takes a value x and returns
  -- a transition that outputs x while staying in the same state. The bind
  -- operation does function application to the output all the while
  -- transitioning state.
  
  open import Control.Monad
  
  instance
    Monad:State : forall {S} -> Monad Sets (State S)
    Monad:State .return x s = (x , s)
    Monad:State .extend f m = \ s -> let (x , s') = m s in run (f x) s'
  
  -- Applicative instance of State S derived from the monad instance.
  
  open import Control.Applicative
  
  instance
    Applicative:State : forall {S} -> Applicative (State S)
    Applicative:State = Idiom: ap return

open State
  using (
    Monad:State;
    Applicative:State
  )
