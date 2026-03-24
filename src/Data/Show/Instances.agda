module Data.Show.Instances where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Agda.Builtin.Int using ()
open import Agda.Builtin.Float using ()
open import Agda.Builtin.String using ()
open import Data.Show as Show using (Show; show; showsPrec)

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Type

instance
  Show-Void : Show Void
  Show-Void .show = \ ()
  Show-Void .showsPrec = Show.showsPrecDefault

  Show-Unit : Show Unit
  Show-Unit .show _ = "tt"
  Show-Unit .showsPrec = Show.showsPrecDefault

  Show-Bool : Show Bool
  Show-Bool .show b = if b then "true" else "false"
  Show-Bool .showsPrec = Show.showsPrecDefault

  Show-Ordering : Show Ordering
  Show-Ordering .show = \ where
    less -> "less"
    equal -> "equal"
    greater -> "greater"
  Show-Ordering .showsPrec = Show.showsPrecDefault

  Show-Nat : Show Nat
  Show-Nat .show = Agda.Builtin.String.primShowNat
  Show-Nat .showsPrec = Show.showsPrecDefault

  Show-Nat1 : Show Nat1
  Show-Nat1 .show (suc m) = show (Nat.suc m)
  Show-Nat1 .showsPrec = Show.showsPrecDefault

  Show-Int : Show Int
  Show-Int .show = Agda.Builtin.Int.primShowInteger
  Show-Int .showsPrec = Show.showsPrecDefault

  Show-Float : Show Float
  Show-Float .show = Agda.Builtin.Float.primShowFloat
  Show-Float .showsPrec = Show.showsPrecDefault

  Show-Char : Show Char
  Show-Char .show = Agda.Builtin.String.primShowChar
  Show-Char .showsPrec = Show.showsPrecDefault

  Show-String : Show String
  Show-String .show = Agda.Builtin.String.primShowString
  Show-String .showsPrec = Show.showsPrecDefault

  Show-Identity : {{Show a}} -> Show (Identity a)
  Show-Identity .show = Show.showDefault
  Show-Identity .showsPrec prec (asIdentity x) =
    Show.showsUnaryWith showsPrec "asIdentity" prec x

  Show-Const : {{Show a}} -> Show (Const a b)
  Show-Const .show = Show.showDefault
  Show-Const .showsPrec prec x = Show.showsUnaryWith showsPrec "Const" prec x

  Show-Tuple : {{Show a}} -> {{Show b}} -> Show (Tuple a b)
  Show-Tuple .show = Show.showDefault
  Show-Tuple .showsPrec prec (x , y) =
    "(" <> showsPrec prec x <> " , " <> showsPrec prec y <> ")"

  Show-Either : {{Show a}} -> {{Show b}} -> Show (Either a b)
  Show-Either .show = Show.showDefault
  Show-Either .showsPrec prec = \ where
    (left x) -> Show.showsUnaryWith showsPrec "left" prec x
    (right x) -> Show.showsUnaryWith showsPrec "right" prec x

  Show-Maybe : {{Show a}} -> Show (Maybe a)
  Show-Maybe .show = Show.showDefault
  Show-Maybe .showsPrec prec = \ where
    (just x) -> Show.showsUnaryWith showsPrec "just" prec x
    nothing -> "nothing"

  Show-List : {{Show a}} -> Show (List a)
  Show-List .show = Show.showDefault
  Show-List .showsPrec prec = \ where
    [] -> "[]"
    (x :: xs) -> Show.showParen (prec > Show.appPrec)
      (showsPrec Show.appPrec+1 x <> " :: " <> showsPrec 0 xs)