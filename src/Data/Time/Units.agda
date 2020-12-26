{-# OPTIONS --type-in-type #-}

module Data.Time.Units where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

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
  constructor _<s>
  field unSecond : Nat

open Second public

record Millisecond : Set where
  constructor _<ms>
  field unMillisecond : Nat

open Millisecond public

record Microsecond : Set where
  constructor _<μs>
  field unMicrosecond : Nat

open Microsecond public

record Picosecond : Set where
  constructor _<ps>
  field unPicosecond : Nat

open Picosecond public

instance
  TimeUnit-Second : TimeUnit Second
  TimeUnit-Second .toMicroseconds (x <s>) = x * 10 ^ 6
  TimeUnit-Second .fromMicroseconds x = (x / 10 ^ 6) <s>

  TimeUnit-Millisecond : TimeUnit Millisecond
  TimeUnit-Millisecond .toMicroseconds (x <ms>) = x * 10 ^ 3
  TimeUnit-Millisecond .fromMicroseconds x = (x / 10 ^ 3) <ms>

  TimeUnit-Microsecond : TimeUnit Microsecond
  TimeUnit-Microsecond .toMicroseconds (x <μs>) = x
  TimeUnit-Microsecond .fromMicroseconds x = x <μs>

  TimeUnit-Picosecond : TimeUnit Picosecond
  TimeUnit-Picosecond .toMicroseconds (x <ps>) = x / 10 ^ 6
  TimeUnit-Picosecond .fromMicroseconds x = (x * 10 ^ 6) <ps>

  Show-Second : Show Second
  Show-Second .showsPrec d (x <s>) = showsPrec d x <<< showString "s"

  Show-Millisecond : Show Millisecond
  Show-Millisecond .showsPrec d (x <ms>) = showsPrec d x <<< showString "ms"

  Show-Microsecond : Show Microsecond
  Show-Microsecond .showsPrec d (x <μs>) = showsPrec d x <<< showString "μs"

  Show-Picosecond : Show Picosecond
  Show-Picosecond .showsPrec d (x <ps>) = showsPrec d x <<< showString "ps"
