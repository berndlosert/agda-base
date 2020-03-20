{-# OPTIONS --type-in-type #-}

module Control.Monad.Reader where

import Control.Monad.ReaderT as ReaderT
import Prelude

open Prelude
open ReaderT using (ReaderT; ReaderT:)

private
  variable
    A B R R' : Set
    M : Set -> Set

Reader : Set -> Set -> Set
Reader R = ReaderT R Identity

Reader: : {{_ : Monad M}} -> (R -> A) -> Reader R A
Reader: f = ReaderT: (return <<< f)

run : Reader R A -> R -> A
run m = runIdentity <<< ReaderT.run m

map' : (A -> B) -> Reader R A -> Reader R B
map' f = ReaderT.map' (value <<< f <<< runIdentity)

with' : (R' -> R) -> Reader R A -> Reader R' A
with' f m = ReaderT.with' f m
