module Data.String.Show where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Agda.Builtin.Int as Int using ()
open import Agda.Builtin.Float as Float using ()
open import Agda.Builtin.String as String using ()
open import Data.String.Builder

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Type

-------------------------------------------------------------------------------
-- ShowS
-------------------------------------------------------------------------------

abstract
  ShowS : Type
  ShowS = Builder

  showChar : Char -> ShowS
  showChar = singleton

  showString : String -> ShowS
  showString = toBuilder

  fromShowS : ShowS -> String
  fromShowS = fromBuilder

  instance
    Semigroup-ShowS : Semigroup ShowS
    Semigroup-ShowS = Semigroup-Builder

    Monoid-ShowS : Monoid ShowS
    Monoid-ShowS = Monoid-Builder

    FromString-ShowS : FromString ShowS
    FromString-ShowS = FromString-Builder

    FromString-Constraint-ShowS : {s : String} -> FromString.Constraint FromString-ShowS s
    FromString-Constraint-ShowS = _

-------------------------------------------------------------------------------
-- Show
-------------------------------------------------------------------------------

record Show (a : Type) : Type where
  field
    show : a -> String
    showsPrec : Nat -> a -> ShowS

  shows : a -> ShowS
  shows = showsPrec 0

  showDefault : a -> String
  showDefault = fromShowS <<< shows

  showsPrecDefault : Nat -> a -> ShowS
  showsPrecDefault _ = showString <<< show

open Show {{...}} public

showParen : Bool -> ShowS -> ShowS
showParen b p = if b then "(" <> p <> ")" else p

appPrec appPrec+1 : Nat
appPrec = 10
appPrec+1 = 11

showsUnaryWith : (Nat -> a -> ShowS) -> ShowS -> Nat -> a -> ShowS
showsUnaryWith sp name prec x = showParen (prec > appPrec)
  (name <> showChar ' ' <> sp appPrec+1 x)

showsBinaryWith : (Nat -> a -> ShowS) -> (Nat -> b -> ShowS)
  -> ShowS -> Nat -> a -> b -> ShowS
showsBinaryWith sp1 sp2 name d x y = showParen (d > appPrec)
  (name <> showChar ' ' <> sp1 appPrec+1 x <> showChar ' ' <> sp2 appPrec+1 y)

module Instances where
  instance
    Show-Void : Show Void
    Show-Void .show = \ ()
    Show-Void .showsPrec = showsPrecDefault

    Show-Unit : Show Unit
    Show-Unit .show _ = "tt"
    Show-Unit .showsPrec = showsPrecDefault

    Show-Bool : Show Bool
    Show-Bool .show b = if b then "true" else "false"
    Show-Bool .showsPrec = showsPrecDefault

    Show-Ordering : Show Ordering
    Show-Ordering .show = \ where
      less -> "less"
      equal -> "equal"
      greater -> "greater"
    Show-Ordering .showsPrec = showsPrecDefault

    Show-Nat : Show Nat
    Show-Nat .show = String.primShowNat
    Show-Nat .showsPrec = showsPrecDefault

    Show-Nat1 : Show Nat1
    Show-Nat1 .show (suc m) = show (Nat.suc m)
    Show-Nat1 .showsPrec = showsPrecDefault

    Show-Int : Show Int
    Show-Int .show = Int.primShowInteger
    Show-Int .showsPrec = showsPrecDefault

    Show-Float : Show Float
    Show-Float .show = Float.primShowFloat
    Show-Float .showsPrec = showsPrecDefault

    Show-Char : Show Char
    Show-Char .show = String.primShowChar
    Show-Char .showsPrec = showsPrecDefault

    Show-String : Show String
    Show-String .show = String.primShowString
    Show-String .showsPrec = showsPrecDefault

    Show-String1 : Show String1
    Show-String1 .show s = show (fromString1 s)
    Show-String1 .showsPrec = showsPrecDefault

    Show-Identity : {{Show a}} -> Show (Identity a)
    Show-Identity .show = showDefault
    Show-Identity .showsPrec prec (asIdentity x) =
      showsUnaryWith showsPrec "asIdentity" prec x

    Show-Const : {{Show a}} -> Show (Const a b)
    Show-Const .show = showDefault
    Show-Const .showsPrec prec x = showsUnaryWith showsPrec "Const" prec x

    Show-Tuple : {{Show a}} -> {{Show b}} -> Show (Tuple a b)
    Show-Tuple .show = showDefault
    Show-Tuple .showsPrec prec (x , y) =
      "(" <> showsPrec prec x <> " , " <> showsPrec prec y <> ")"

    Show-Either : {{Show a}} -> {{Show b}} -> Show (Either a b)
    Show-Either .show = showDefault
    Show-Either .showsPrec prec = \ where
      (left x) -> showsUnaryWith showsPrec "left" prec x
      (right x) -> showsUnaryWith showsPrec "right" prec x

    Show-Maybe : {{Show a}} -> Show (Maybe a)
    Show-Maybe .show = showDefault
    Show-Maybe .showsPrec prec = \ where
      (just x) -> showsUnaryWith showsPrec "just" prec x
      nothing -> "nothing"

    Show-List : {{Show a}} -> Show (List a)
    Show-List .show = showDefault
    Show-List .showsPrec prec = \ where
      [] -> "[]"
      (x :: xs) -> showParen (prec > appPrec)
        (showsPrec appPrec+1 x <> " :: " <> showsPrec 0 xs)

    Show-List1 : {{Show a}} -> Show (List1 a)
    Show-List1 .show = showDefault
    Show-List1 .showsPrec prec (x :: xs) = showParen (prec > appPrec)
      (showsPrec appPrec+1 x <> " :: " <> showsPrec 0 xs)
