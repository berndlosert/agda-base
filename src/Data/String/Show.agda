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
    a b : Set

-------------------------------------------------------------------------------
-- Show
-------------------------------------------------------------------------------

record Show (a : Set) : Set where
  field
    show : a -> String
    showsPrec : Nat -> a -> Builder

  showDefault : a -> String
  showDefault = fromBuilder <<< showsPrec 0

  showsPrecDefault : Nat -> a -> Builder
  showsPrecDefault _ = toBuilder <<< show

open Show {{...}} public

showParen : Bool -> Builder -> Builder
showParen b p = if b then "(" <> p <> ")" else p

appPrec appPrec+1 : Nat
appPrec = 10
appPrec+1 = 11

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
    LT -> "LT"
    EQ -> "EQ"
    GT -> "GT"
  Show-Ordering .showsPrec = showsPrecDefault

  Show-Nat : Show Nat
  Show-Nat .show = String.primShowNat
  Show-Nat .showsPrec = showsPrecDefault

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

  Show-Function : Show (Function a b)
  Show-Function .show _ = "<function>"
  Show-Function .showsPrec = showsPrecDefault

  Show-Pair : {{Show a}} -> {{Show b}} -> Show (Pair a b)
  Show-Pair .show = showDefault
  Show-Pair .showsPrec prec (x , y) =
    "(" <> showsPrec prec x <> " , " <> showsPrec prec y <> ")"

  Show-Either : {{Show a}} -> {{Show b}} -> Show (Either a b)
  Show-Either .show = showDefault
  Show-Either .showsPrec prec = \ where
    (left x) -> showParen (prec > appPrec)
      ("left " <> showsPrec appPrec+1 x)
    (right x) -> showParen (prec > appPrec)
      ("right " <> showsPrec appPrec+1 x)

  Show-Maybe : {{Show a}} -> Show (Maybe a)
  Show-Maybe .show = showDefault
  Show-Maybe .showsPrec prec = \ where
    (just x) -> showParen (prec > appPrec)
      ("just " <> showsPrec appPrec+1 x)
    nothing -> "nothing"

  Show-List : {{Show a}} -> Show (List a)
  Show-List .show = showDefault
  Show-List .showsPrec prec = \ where
    [] -> "[]"
    (x :: xs) -> showParen (prec > appPrec)
      (showsPrec appPrec+1 x <> " :: " <> showsPrec 0 xs)
