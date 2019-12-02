{-# OPTIONS --type-in-type #-}

module Data.Nat where

open import Data.Nat.Base public

-- For some odd reason, we have to define Number:Nat in order for other modules
-- to define instances of Number without getting a "No instance of type
-- (Number Nat) was found in scope" error.

open import Data.Unit public
open import Notation.Number public

Number:Nat : Number Nat
Number:Nat = record {
     Constraint = \ _ -> Unit;
     fromNat = \ n -> n
   }

-- Used for telling Agda that a number literal is a Nat.

Nat: : Nat -> Nat
Nat: x = x

-- Division of natural numbers.

open import Notation.Div public
open import Data.Void

instance
  Div:Nat : Div Nat
  Div:Nat = record {
      Constraint = \ { zero -> Void; (suc n) -> Unit };
      _/_ = \ { m (suc n) -> div-helper zero n m n }
    }

-- The mod operation for natural numbers.

open import Notation.Mod public

instance
  Mod:Nat : Mod Nat
  Mod:Nat = record {
      Constraint = \ { zero -> Void; (suc n) -> Unit };
      _%_ = \ { m (suc n) -> mod-helper zero n m n }
    }

-- The natural numbers form a semigroup under addition.

open import Data.Semigroup

instance
  Semigroup:Nat : Semigroup Nat
  Semigroup:Nat = Semigroup: _+_

-- Since 0 is the identity of addition, the natural numbers form a monoid.

open import Data.Monoid

instance
  Monoid:Nat : Monoid Nat
  Monoid:Nat = Monoid: zero
