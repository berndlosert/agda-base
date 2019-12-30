{-# OPTIONS --type-in-type #-}

module Data.Nat where

open import Data.Nat.Base public
  hiding (module Nat)

module Nat where

  import Agda.Builtin.Nat as Builtin

  -- Defines _+_ as addition.
  
  open import Notation.Add
  
  instance
    Add:Nat : Add Nat
    Add:Nat = Add: Builtin._+_
  
  -- Defines _-_ as subtraction.
  
  open import Notation.Sub
  
  instance
    Sub:Nat : Sub Nat
    Sub:Nat = Sub: Builtin._-_ 
  
  -- Defines _*_ as multiplication.
  
  open import Notation.Mul
  
  instance
    Mul:Nat : Mul Nat
    Mul:Nat = Mul: Builtin._*_ 
  
  -- Defines _==_ for equality.
  
  open import Data.Eq
  
  instance
    Eq:Nat : Eq Nat
    Eq:Nat = Eq: Builtin._==_ 
  
  -- Defines _<_ and related comparison operations.
  
  open import Data.Ord
  
  instance
    Ord:Nat : Ord Nat
    Ord:Nat = Ord: Builtin._<_ 

  -- For some odd reason, we have to define Number:Nat in order for other
  -- modules to define instances of Number without getting a "No instance of
  -- type (Number Nat) was found in scope" error.

  open import Data.Unit
  open import Notation.Number
  
  instance
    Number:Nat : Number Nat
    Number:Nat = record {
         Constraint = \ _ -> Unit;
         fromNat = \ n -> n
       }
  
  -- Division of natural numbers.
  
  open import Notation.Div
  open import Data.Void
  
  instance
    Div:Nat : Div Nat
    Div:Nat = record {
        Constraint = \ { zero -> Void; (suc n) -> Unit };
        _/_ = \ { m (suc n) -> Builtin.div-helper zero n m n }
      }
  
  -- The mod operation for natural numbers.
  
  open import Notation.Mod
  
  instance
    Mod:Nat : Mod Nat
    Mod:Nat = record {
        Constraint = \ { zero -> Void; (suc n) -> Unit };
        _%_ = \ { m (suc n) -> Builtin.mod-helper zero n m n }
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

open Nat public
  using (
    Add:Nat;
    Sub:Nat;
    Mul:Nat;
    Eq:Nat;
    Ord:Nat;
    Number:Nat;
    Div:Nat; 
    Mod:Nat;
    Semigroup:Nat;
    Monoid:Nat
  )
