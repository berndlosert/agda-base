{-# OPTIONS --type-in-type #-}

module Data.Time.Units where

open import Prelude

--------------------------------------------------------------------------------
-- TimeUnit
--------------------------------------------------------------------------------

record TimeUnit (a : Set) : Set where
  field
    toMicroseconds : a -> Nat
    fromMicroseconds : Nat -> a

open TimeUnit {{...}} public

--------------------------------------------------------------------------------
-- Second, Millisecond, Microsecond
--------------------------------------------------------------------------------

data Second : Set where
  _sec : Nat -> Second

data Millisecond : Set where
  _msec : Nat -> Millisecond

data Microsecond : Set where
  _μsec : Nat -> Microsecond

instance
  timeUnitSecond : TimeUnit Second
  timeUnitSecond .toMicroseconds (x sec) = x * 10 ^ 6
  timeUnitSecond .fromMicroseconds x = (x / 10 ^ 6) sec

  timeUnitMillisecond : TimeUnit Millisecond
  timeUnitMillisecond .toMicroseconds (x msec) = x * 10 ^ 3
  timeUnitMillisecond .fromMicroseconds x = (x / 10 ^ 3) msec

  timeUnitMicrosecond : TimeUnit Microsecond
  timeUnitMicrosecond .toMicroseconds (x μsec) = x * 10 ^ 3
  timeUnitMicrosecond .fromMicroseconds x = (x / 10 ^ 3) μsec
