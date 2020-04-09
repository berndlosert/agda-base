{-# OPTIONS --type-in-type #-}

module String.Show where

private variable A B : Set

open import Data.Bool
open import Data.Char
open import Data.Either
open import Data.Float
open import Data.Int
open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.Pair
open import Data.Sequence
open import Data.String
open import Data.Unit
open import Data.Void

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
  showNat .show = primShowNat
    where open import Agda.Builtin.String

  showInt : Show Int
  showInt .show = primShowInteger
    where open import Agda.Builtin.Int

  showFloat : Show Float
  showFloat .show = primShowFloat
    where open import Agda.Builtin.Float

  showPair : {{_ : Show A}} {{_ : Show B}} -> Show (Pair A B)
  showPair .show (x , y) = "(" ++ show x ++ " , " ++ show y ++ ")"

  showEither : {{_ : Show A}} {{_ : Show B}} -> Show (Either A B)
  showEither .show = \ where
    (left x) -> "left " ++ show x
    (right y) -> "right " ++ show y

  showMaybe : {{_ : Show A}} -> Show (Maybe A)
  showMaybe .show = \ where
    (just x) -> "just " ++ show x
    nothing -> "nothing"

  showList : forall {A} {{_ : Show A}} -> Show (List A)
  showList .show [] = "[]"
  showList {A} .show as = "(" ++ show' as ++ ")"
    where
      show' : List A -> String
      show' [] = "[]"
      show' (x :: xs) = show x ++ " :: " ++ show' xs

  showChar : Show Char
  showChar .show c = "'" ++ singleton c ++ "'"

  showString : Show String
  showString .show = primShowString
    where open import Agda.Builtin.String
