{-# OPTIONS --type-in-type #-}

module Data.Digit where

module Base where

  -- Digit is used to represent the decimal digits.
  
  data Digit : Set where
    0d 1d 2d 3d 4d 5d 6d 7d 8d 9d : Digit

open Base public
  hiding (module Digit)

module Digit where

  -- This is how we compare digits for equality.
  
  open import Data.Bool
  open import Data.Eq
  
  instance
    Eq:Digit : Eq Digit
    Eq:Digit = Eq: \ where
      0d 0d -> true
      1d 1d -> true
      2d 2d -> true
      3d 3d -> true
      4d 4d -> true
      5d 5d -> true
      6d 6d -> true
      7d 7d -> true
      8d 8d -> true
      9d 9d -> true
      _ _ -> false
  
  -- This is how we compare digits in general.
  
  open import Data.Ord
  
  instance
    Ord:Digit : Ord Digit
    Ord:Digit = Ord: \ where
  
      0d 0d -> false
      0d _ -> true
  
      1d 0d -> false
      1d 1d -> false
      1d _ -> true
  
      2d 0d -> false
      2d 1d -> false
      2d 2d -> false
      2d _ -> true
  
      3d 0d -> false
      3d 1d -> false
      3d 2d -> false
      3d 3d -> false
      3d _ -> true
  
      4d 5d -> true
      4d 6d -> true
      4d 7d -> true
      4d 8d -> true
      4d 9d -> true
      4d _ -> false
  
      5d 6d -> true
      5d 7d -> true
      5d 8d -> true
      5d 9d -> true
      5d _ -> false
  
      6d 7d -> true
      6d 8d -> true
      6d 9d -> true
      6d _ -> false
  
      7d 8d -> true
      7d 9d -> true
      7d _ -> false
  
      8d 9d -> true
      8d _ -> false
  
      9d _ -> false
  
  -- Adding two digits m and n yields a pair of digits (sum , cout).
  
  open import Data.Product
  
  halfAdd : Digit -> Digit -> Digit * Digit
  
  halfAdd 0d 0d = (0d , 0d)
  halfAdd 0d 1d = (1d , 0d)
  halfAdd 0d 2d = (2d , 0d)
  halfAdd 0d 3d = (3d , 0d)
  halfAdd 0d 4d = (4d , 0d)
  halfAdd 0d 5d = (5d , 0d)
  halfAdd 0d 6d = (6d , 0d)
  halfAdd 0d 7d = (7d , 0d)
  halfAdd 0d 8d = (8d , 0d)
  halfAdd 0d 9d = (9d , 0d)
  
  halfAdd 1d 0d = (1d , 0d)
  halfAdd 1d 1d = (2d , 0d)
  halfAdd 1d 2d = (3d , 0d)
  halfAdd 1d 3d = (4d , 0d)
  halfAdd 1d 4d = (5d , 0d)
  halfAdd 1d 5d = (6d , 0d)
  halfAdd 1d 6d = (7d , 0d)
  halfAdd 1d 7d = (8d , 0d)
  halfAdd 1d 8d = (9d , 0d)
  halfAdd 1d 9d = (0d , 1d)
  
  halfAdd 2d 0d = (2d , 0d)
  halfAdd 2d 1d = (3d , 0d)
  halfAdd 2d 2d = (4d , 0d)
  halfAdd 2d 3d = (5d , 0d)
  halfAdd 2d 4d = (6d , 0d)
  halfAdd 2d 5d = (7d , 0d)
  halfAdd 2d 6d = (8d , 0d)
  halfAdd 2d 7d = (9d , 0d)
  halfAdd 2d 8d = (0d , 1d)
  halfAdd 2d 9d = (1d , 2d)
  
  halfAdd 3d 0d = (3d , 0d)
  halfAdd 3d 1d = (4d , 0d)
  halfAdd 3d 2d = (5d , 0d)
  halfAdd 3d 3d = (6d , 0d)
  halfAdd 3d 4d = (7d , 0d)
  halfAdd 3d 5d = (8d , 0d)
  halfAdd 3d 6d = (9d , 0d)
  halfAdd 3d 7d = (0d , 1d)
  halfAdd 3d 8d = (1d , 1d)
  halfAdd 3d 9d = (2d , 1d)
  
  halfAdd 4d 0d = (4d , 0d)
  halfAdd 4d 1d = (5d , 0d)
  halfAdd 4d 2d = (6d , 0d)
  halfAdd 4d 3d = (7d , 0d)
  halfAdd 4d 4d = (8d , 0d)
  halfAdd 4d 5d = (9d , 0d)
  halfAdd 4d 6d = (0d , 1d)
  halfAdd 4d 7d = (1d , 1d)
  halfAdd 4d 8d = (2d , 1d)
  halfAdd 4d 9d = (3d , 1d)
  
  halfAdd 5d 0d = (5d , 0d)
  halfAdd 5d 1d = (6d , 0d)
  halfAdd 5d 2d = (7d , 0d)
  halfAdd 5d 3d = (8d , 0d)
  halfAdd 5d 4d = (9d , 0d)
  halfAdd 5d 5d = (0d , 1d)
  halfAdd 5d 6d = (1d , 1d)
  halfAdd 5d 7d = (2d , 1d)
  halfAdd 5d 8d = (3d , 1d)
  halfAdd 5d 9d = (4d , 1d)
  
  halfAdd 6d 0d = (6d , 0d)
  halfAdd 6d 1d = (7d , 0d)
  halfAdd 6d 2d = (8d , 0d)
  halfAdd 6d 3d = (9d , 0d)
  halfAdd 6d 4d = (0d , 1d)
  halfAdd 6d 5d = (1d , 1d)
  halfAdd 6d 6d = (2d , 1d)
  halfAdd 6d 7d = (3d , 1d)
  halfAdd 6d 8d = (4d , 1d)
  halfAdd 6d 9d = (5d , 1d)
  
  halfAdd 7d 0d = (7d , 0d)
  halfAdd 7d 1d = (8d , 0d)
  halfAdd 7d 2d = (9d , 0d)
  halfAdd 7d 3d = (0d , 1d)
  halfAdd 7d 4d = (1d , 1d)
  halfAdd 7d 5d = (2d , 1d)
  halfAdd 7d 6d = (3d , 1d)
  halfAdd 7d 7d = (4d , 1d)
  halfAdd 7d 8d = (5d , 1d)
  halfAdd 7d 9d = (6d , 1d)
  
  halfAdd 8d 0d = (8d , 0d)
  halfAdd 8d 1d = (9d , 0d)
  halfAdd 8d 2d = (0d , 1d)
  halfAdd 8d 3d = (1d , 1d)
  halfAdd 8d 4d = (2d , 1d)
  halfAdd 8d 5d = (3d , 1d)
  halfAdd 8d 6d = (4d , 1d)
  halfAdd 8d 7d = (5d , 1d)
  halfAdd 8d 8d = (6d , 1d)
  halfAdd 8d 9d = (7d , 1d)
  
  halfAdd 9d 0d = (9d , 0d)
  halfAdd 9d 1d = (0d , 1d)
  halfAdd 9d 2d = (1d , 1d)
  halfAdd 9d 3d = (2d , 1d)
  halfAdd 9d 4d = (3d , 1d)
  halfAdd 9d 5d = (4d , 1d)
  halfAdd 9d 6d = (5d , 1d)
  halfAdd 9d 7d = (6d , 1d)
  halfAdd 9d 8d = (7d , 1d)
  halfAdd 9d 9d = (8d , 1d)
  
  -- Adding three digits m, n, cin yields a pair (sum , cout).
  fullAdd : Digit -> Digit -> Digit -> Digit * Digit
  fullAdd m n cin =
    let
      (sum1 , cout1) = halfAdd m n
      (sum , cout2) = halfAdd sum1 cin
      cout = max cout1 cout2
    in
      (sum , cout)
  
  -- Convert a Digit to a Char.
  
  open import Data.Char
  open import Data.Function
  
  toChar : Digit -> Char
  toChar d = case d of \ where
    0d -> '0'
    1d -> '1'
    2d -> '2'
    3d -> '3'
    4d -> '4'
    5d -> '5'
    6d -> '6'
    7d -> '7'
    8d -> '8'
    9d -> '9'
  
  -- Parse a Char into a Digit. 
  
  open import Data.Maybe
  
  fromChar : Char -> Maybe Digit
  fromChar c = case c of \ where 
    '0' -> just 0d
    '1' -> just 1d
    '2' -> just 2d
    '3' -> just 3d
    '4' -> just 4d
    '5' -> just 5d
    '6' -> just 6d
    '7' -> just 7d
    '8' -> just 8d
    '9' -> just 9d
    _ -> nothing
  
  -- Convert a Digit to a Nat.
  
  open import Data.Nat.Base
  
  toNat : Digit -> Nat
  toNat d = case d of \ where
    0d -> 0
    1d -> 1
    2d -> 2
    3d -> 3
    4d -> 4
    5d -> 5
    6d -> 6
    7d -> 7
    8d -> 8
    9d -> 9
  
open Digit public
  using (Eq:Digit; Ord:Digit)
