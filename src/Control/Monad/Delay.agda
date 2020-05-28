{-# OPTIONS --type-in-type #-}

module Control.Monad.Delay where

open import Prelude

open import Control.Size
open import Control.Thunk

-- Delay represents processes which must always eventually yield. It is the
-- final coalgebra of the functor X +_.

data Delay (i : Size) (X : Set) : Set where
  now : X -> Delay i X
  later : Thunk i Delay X -> Delay i X

-- Since Delay is a final coalgebra, it has an unfold operation.

unfold : forall {i X Y} -> (Y -> X + Y) -> Y -> Delay i X
unfold f y = either now (\ x -> later \ where .force -> unfold f x) $ f y

-- Run a Delay process for at most n steps.

runFor : Nat -> forall {X} -> Delay _ X -> Maybe X
runFor _ (now x) = just x
runFor zero (later _) = nothing
runFor (suc n) (later thunk) = runFor n (force thunk)

-- Imagine a stream of Maybe X values. We model the stream as a function of
-- type Nat -> Maybe X. Assuming there is a least n : Nat such that the nth
-- element of the stream is a (just x) value, tryMore will produce a Delay
-- value d such that runFor n d = just x.

tryMore : forall {i X} -> (Nat -> Maybe X) -> Delay i X
tryMore {_} {X} f = unfold try zero
  where
    try : Nat -> X + Nat
    try n with f n
    ... | just x = left x
    ... | nothing = right (suc n)

open import Data.Bool

-- This is just like tryMore, except that now we have a stream of Bool values,
-- modelled using a function of type Nat -> Bool.

minimize : (Nat -> Bool) -> Delay _ Nat
minimize test = tryMore (\ n -> if test n then just n else nothing)

instance
  functorDelay : {i : Size} -> Functor (Delay i)
  functorDelay .map f (now x) = now (f x)
  functorDelay .map f (later thunk) =
    later \ where .force -> map f (force thunk)

  monadDelay : {i : Size} -> Monad (Delay i)
  monadDelay .return = now
  monadDelay .extend f (now x) = f x
  monadDelay .extend f (later thunk) = later \ where
    .force -> extend f (force thunk)
