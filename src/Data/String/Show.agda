{-# OPTIONS --type-in-type #-}

module Data.String.Show where

open import Agda.Builtin.String using (primShowNat)
open import Agda.Builtin.Int using (primShowInteger)
open import Agda.Builtin.Float using (primShowFloat)
open import Control.Applicative using (pure)
open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.Either using (Either; left; right)
open import Data.Eq using (Eq)
open import Data.Float using (Float)
open import Data.Int using (Int)
open import Data.List using (List; _::_; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (Nat)
open import Data.Pair using (Pair; _,_)
open import Data.Semigroup using (_<>_)
open import Data.Semiring using (_+_)
open import Data.String using (String; pack)
open import Data.Unit using (Unit; unit)
open import Data.Void using (Void)

private variable A B : Set

record Show (A : Set) : Set where
  field
    show : A -> String

open Show {{...}} public

instance
  showVoid : Show Void
  showVoid .show ()

  showUnit : Show Unit
  showUnit .show unit = "unit"

  showBool : Show Bool
  showBool .show = \ where
    true -> "true"
    false -> "false"

  showNat : Show Nat
  showNat .show = primShowNat

  showInt : Show Int
  showInt .show = primShowInteger

  showFloat : Show Float
  showFloat .show = primShowFloat

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
  showChar .show c = "'" <> pack (pure c) <> "'"

  showString : Show String
  showString .show = Agda.Builtin.String.primShowString


