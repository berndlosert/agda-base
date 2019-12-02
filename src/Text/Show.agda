{-# OPTIONS --type-in-type #-}

module Text.Show where

open import Agda.Builtin.Int
open import Data.Bool
open import Data.Cast
open import Data.Digit
open import Data.Decimal
open import Data.Function
open import Data.List
open import Data.Maybe
open import Data.Nat.Base
open import Data.Product
open import Data.String

-- Conversion of values to readable Strings.
record Show (X : Set) : Set where
  constructor Show:
  field
    show : X -> String

open Show {{...}} public

instance
  -- Pretty-print Bool values.
  Show:Bool : Show Bool
  Show:Bool = Show: λ where
    true -> "true"
    false -> "false"

  -- Pretty-print Digit values.
  Show:Digit : Show Digit
  Show:Digit = Show: λ where
    0d -> "0"
    1d -> "1"
    2d -> "2"
    3d -> "3"
    4d -> "4"
    5d -> "5"
    6d -> "6"
    7d -> "7"
    8d -> "8"
    9d -> "9"

  -- Pretty-print Decimal values.
  Show:Decimal : Show Decimal
  Show:Decimal .show [] = ""
  Show:Decimal .show (0d :: []) = "0"
  Show:Decimal .show (x :: xs) = show xs ++ show x

  -- Pretty-print Nat values. 
  Show:Nat : Show Nat
  Show:Nat = Show: λ n -> show (cast {Nat} {Decimal} n)

  -- Pretty-print Int values.
  Show:Int : Show Int
  Show:Int = Show: primShowInteger

  -- Pretty-print String values.
  Show:String : Show String
  Show:String = Show: primShowString

  -- Pretty-print pairs.
  Show:Product : {X Y : Set} {{_ : Show X}} {{_ : Show Y}}
    -> Show (X * Y)
  Show:Product = Show: λ where
    (x , y) -> "( " ++ show x ++ " , " ++ show y ++ " )"

  -- Pretty-print Maybe values.
  Show:Maybe : {X : Set} {{_ : Show X}} -> Show (Maybe X)
  Show:Maybe = Show: λ where
    (just x) -> "just " ++ show x
    nothing -> "nothing"

  -- Pretty-print lists.
  Show:List : {X : Set} {{_ : Show X}} -> Show (List X)
  Show:List = Show: λ { [] -> "[]"; xs -> "[ " ++ csv xs ++ " ]" }
    where
      csv : {X : Set} {{_ : Show X}} -> List X -> String
      csv [] = ""
      csv (x :: []) = show x
      csv (x :: xs) = show x ++ " # " ++ csv xs
