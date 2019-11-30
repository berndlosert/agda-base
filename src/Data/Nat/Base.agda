{-# OPTIONS --type-in-type #-}

module Data.Nat.Base where

-- The type Nat of unary natural numbers has two constructors: zero
-- (for 0) and suc (for successor).
open import Agda.Builtin.Nat public
  using (Nat; zero; suc; div-helper; mod-helper)
open import Agda.Builtin.Nat
  renaming (
    _+_ to addNat; 
    _-_ to subNat;
    _*_ to mulNat;
    _==_ to eqNat;
    _<_ to ltNat
  )

-- Defines + as addition.
open import Notation.Add public
instance Add:Nat : Add Nat
Add:Nat = Add: addNat

-- Defines - as subtraction.
open import Notation.Sub public
instance Sub:Nat : Sub Nat
Sub:Nat = Sub: subNat

-- Defines * as multiplication.
open import Notation.Mul public
instance Mul:Nat : Mul Nat
Mul:Nat = Mul: mulNat

-- Defines _==_ for equality.
open import Data.Eq public
instance Eq:Nat : Eq Nat
Eq:Nat = Eq: eqNat

-- Defines _<_ and related comparison operations.
open import Data.Ord public
instance Ord:Nat : Ord Nat
Ord:Nat = Ord: ltNat 
