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

record Second : Set where
  constructor _sec
  field unSecond : Nat

open Second public

record Millisecond : Set where
  constructor _msec
  field unMillisecond : Nat

open Millisecond public

record Microsecond : Set where
  constructor _μsec
  field unMicrosecond : Nat

open Microsecond public

record Picosecond : Set where
  constructor _psec
  field unPicosecond : Nat

open Picosecond public

instance
  timeUnitSecond : TimeUnit Second
  timeUnitSecond .toMicroseconds (x sec) = x * 10 ^ 6
  timeUnitSecond .fromMicroseconds x = (x / 10 ^ 6) sec

  timeUnitMillisecond : TimeUnit Millisecond
  timeUnitMillisecond .toMicroseconds (x msec) = x * 10 ^ 3
  timeUnitMillisecond .fromMicroseconds x = (x / 10 ^ 3) msec

  timeUnitMicrosecond : TimeUnit Microsecond
  timeUnitMicrosecond .toMicroseconds (x μsec) = x
  timeUnitMicrosecond .fromMicroseconds x = x μsec

  timeUnitPicosecond : TimeUnit Picosecond
  timeUnitPicosecond .toMicroseconds (x psec) = x / 10 ^ 6
  timeUnitPicosecond .fromMicroseconds x = (x * 10 ^ 6) psec

  showSecond : Show Second
  showSecond .show (x sec) = show x ++ "s"

  showMillisecond : Show Millisecond
  showMillisecond .show (x msec) = show x ++ "ms"

  showMicrosecond : Show Microsecond
  showMicrosecond .show (x μsec) = show x ++ "μs"

  showPicosecond : Show Picosecond
  showPicosecond .show (x psec) = show x ++ "ps"
