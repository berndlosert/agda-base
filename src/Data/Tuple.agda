{-# OPTIONS --type-in-type #-}

module Data.Tuple where

open import Data.Nat
open import Data.Pair
open import Data.Unit
open import Notation.Exp
open import Notation.Mul

-- Define X ^ n to be the type of all n-tuples on X.

instance
  Exp:Tuple : Exp Set Nat Set
  Exp:Tuple ._^_ X zero = Unit
  Exp:Tuple ._^_ X (suc zero) = X 
  Exp:Tuple ._^_ X (suc (suc n)) = X * X ^ (suc n)

-- Left-to-right associativity of _*_.

assoc : forall {X Y Z} -> (X * Y) * Z -> X * Y * Z
assoc ((x , y) , z) = (x , y , z)

cons : forall {n X} -> X -> X ^ n -> X ^ suc n
cons {zero} x _  = x
cons {suc n} x xs = (x , xs)

-- Proof that X ^ m * X ^ n and X ^ (m + n) are isomorphic.

open import Notation.Add
open import Notation.Append

append : {m n : Nat} {X : Set} -> X ^ m -> X ^ n -> X ^ (m + n)
append {zero} {n} xs ys = ys
append {suc zero} {n} x ys = cons {n} x ys
append {suc (suc m)} {n} (x , xs) ys = (x , append {suc m} {n} xs ys)
      
instance
  Append:Tuple : {m n : Nat} {X : Set} -> Append (X ^ m) (X ^ n) (X ^ (m + n))
  Append:Tuple {m} {n} {X} ._++_ xs ys = append {m} {n} {X} xs ys
