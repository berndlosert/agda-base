{-# OPTIONS --type-in-type #-}

module Data.String.Show where

private variable A B : Set

open import Data.Char
open import Data.Float
open import Data.Int
open import Data.List
open import Data.Nat
open import Data.String

open import Prelude

record Show (A : Set) : Set where
  field show : A -> String

open Show {{...}} public

instance
  showVoid : Show Void
  showVoid .show ()

  showUnit : Show Unit
  showUnit .show unit = "unit"

  showBool : Show Bool
  showBool .show true = "true"
  showBool .show false = "false"

  showNat : Show Nat
  showNat .show = Nat.show

  showInt : Show Int
  showInt .show = Int.show

  showFloat : Show Float
  showFloat .show = Float.show

  showPair : {{_ : Show A}} {{_ : Show B}} -> Show (Pair A B)
  showPair .show (x , y) = "(" <> show x <> " , " <> show y <> ")"

  showEither : {{_ : Show A}} {{_ : Show B}} -> Show (Either A B)
  showEither .show = \ where
    (left x) -> "left " <> show x
    (right y) -> "right " <> show y

  showMaybe : {{_ : Show A}} -> Show (Maybe A)
  showMaybe .show = \ where
    (just x) -> "just " <> show x
    nothing -> "nothing"

  showList : forall {A} {{_ : Show A}} -> Show (List A)
  showList .show [] = "[]"
  showList {A} .show as = "(" <> show' as <> ")"
    where
      show' : List A -> String
      show' [] = "[]"
      show' (x :: xs) = show x <> " :: " <> show' xs

  showChar : Show Char
  showChar .show c = "'" <> String.fromChar c <> "'"

  showString : Show String
  showString .show = String.show
