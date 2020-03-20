{-# OPTIONS --type-in-type #-}

module Control.Monad.State where

import Control.Monad.StateT as StateT
import Prelude

open Prelude
open StateT using (StateT; state)

private
  variable
    A B S : Set
    M : Set -> Set

State : Set -> Set -> Set
State S = StateT S Identity

State: : {{_ : Monad M}} -> (S -> A * S) -> State S A
State: = state

run : State S A -> S -> A * S
run m = Identity.run <<< StateT.run m

eval : State S A -> S -> A
eval m s = fst (run m s)

exec : State S A -> S -> S
exec m s = snd (run m s)

map' : (A * S -> B * S) -> State S A -> State S B
map' f = StateT.map' (value <<< f <<< Identity.run)

with' : (S -> S) -> State S A -> State S A
with' = StateT.with'

get : State S S
get = StateT.get

put : S -> State S Unit
put = StateT.put

modify : (S -> S) -> State S Unit
modify = StateT.modify

gets : (S -> A) -> State S A
gets = StateT.gets
