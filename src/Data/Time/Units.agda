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
  TimeUnit-Second : TimeUnit Second
  TimeUnit-Second .toMicroseconds (x sec) = x * 10 ^ 6
  TimeUnit-Second .fromMicroseconds x = (x / 10 ^ 6) sec

  TimeUnit-Millisecond : TimeUnit Millisecond
  TimeUnit-Millisecond .toMicroseconds (x msec) = x * 10 ^ 3
  TimeUnit-Millisecond .fromMicroseconds x = (x / 10 ^ 3) msec

  TimeUnit-Microsecond : TimeUnit Microsecond
  TimeUnit-Microsecond .toMicroseconds (x μsec) = x
  TimeUnit-Microsecond .fromMicroseconds x = x μsec

  TimeUnit-Picosecond : TimeUnit Picosecond
  TimeUnit-Picosecond .toMicroseconds (x psec) = x / 10 ^ 6
  TimeUnit-Picosecond .fromMicroseconds x = (x * 10 ^ 6) psec

  Show-Second : Show Second
  Show-Second .showsPrec d (x sec) = showsPrec d x ∘ showString "s"

  Show-Millisecond : Show Millisecond
  Show-Millisecond .showsPrec d (x msec) = showsPrec d x ∘ showString "ms"

  Show-Microsecond : Show Microsecond
  Show-Microsecond .showsPrec d (x μsec) = showsPrec d x ∘ showString "μs"

  Show-Picosecond : Show Picosecond
  Show-Picosecond .showsPrec d (x psec) = showsPrec d x ∘ showString "ps"
