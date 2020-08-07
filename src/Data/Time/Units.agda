module Data.Time.Units where

open import Prelude

-------------------------------------------------------------------------------
-- TimeUnit
-------------------------------------------------------------------------------

record TimeUnit (a : Set) : Set where
  field
    toMicroseconds : a -> Nat
    fromMicroseconds : Nat -> a

open TimeUnit {{...}} public

-------------------------------------------------------------------------------
-- Second, Millisecond, Microsecond
-------------------------------------------------------------------------------

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
  TimeUnitSecond : TimeUnit Second
  TimeUnitSecond .toMicroseconds (x sec) = x * 10 ^ 6
  TimeUnitSecond .fromMicroseconds x = (x / 10 ^ 6) sec

  TimeUnitMillisecond : TimeUnit Millisecond
  TimeUnitMillisecond .toMicroseconds (x msec) = x * 10 ^ 3
  TimeUnitMillisecond .fromMicroseconds x = (x / 10 ^ 3) msec

  TimeUnitMicrosecond : TimeUnit Microsecond
  TimeUnitMicrosecond .toMicroseconds (x μsec) = x
  TimeUnitMicrosecond .fromMicroseconds x = x μsec

  TimeUnitPicosecond : TimeUnit Picosecond
  TimeUnitPicosecond .toMicroseconds (x psec) = x / 10 ^ 6
  TimeUnitPicosecond .fromMicroseconds x = (x * 10 ^ 6) psec

  ShowSecond : Show Second
  ShowSecond .showsPrec d (x sec) = showsPrec d x ∘ showString "s"

  ShowMillisecond : Show Millisecond
  ShowMillisecond .showsPrec d (x msec) = showsPrec d x ∘ showString "ms"

  ShowMicrosecond : Show Microsecond
  ShowMicrosecond .showsPrec d (x μsec) = showsPrec d x ∘ showString "μs"

  ShowPicosecond : Show Picosecond
  ShowPicosecond .showsPrec d (x psec) = showsPrec d x ∘ showString "ps"
