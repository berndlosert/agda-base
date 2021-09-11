{-# OPTIONS --type-in-type #-}

module String.Show where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Agda.Builtin.Int
open import Agda.Builtin.Float
open import Agda.Builtin.String

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Set

-------------------------------------------------------------------------------
-- Show
-------------------------------------------------------------------------------

ShowS : Set
ShowS = String -> String

record Show (a : Set) : Set where
  field showsPrec : Nat -> a -> ShowS

  shows : a -> ShowS
  shows = showsPrec 0

  show : a -> String
  show x = shows x ""

open Show {{...}} public

showString : String -> ShowS
showString = primStringAppend

showParen : Bool -> ShowS -> ShowS
showParen b p = if b then showString "(" <<< p <<< showString ")" else p

appPrec appPrec+1 : Nat
appPrec = 10
appPrec+1 = 11

instance
  Show-Void : Show Void
  Show-Void .showsPrec _ ()

  Show-Unit : Show Unit
  Show-Unit .showsPrec _ tt = showString "tt"

  Show-Bool : Show Bool
  Show-Bool .showsPrec _ b = showString (if b then "true" else "false")

  Show-Ordering : Show Ordering
  Show-Ordering .showsPrec _ = \ where
    LT -> showString "LT"
    EQ -> showString "EQ"
    GT -> showString "GT"

  Show-Nat : Show Nat
  Show-Nat .showsPrec _ = showString <<< primShowNat

  Show-Int : Show Int
  Show-Int .showsPrec _ = showString <<< primShowInteger

  Show-Float : Show Float
  Show-Float .showsPrec _ = showString <<< primShowFloat

  Show-Char : Show Char
  Show-Char .showsPrec _ = showString <<< primShowChar

  Show-String : Show String
  Show-String .showsPrec _ = showString <<< primShowString

  Show-Function : Show (Function a b)
  Show-Function .showsPrec _ _ = showString "<function>"

  Show-Pair : {{Show a}} -> {{Show b}} -> Show (Pair a b)
  Show-Pair .showsPrec d (x , y) = showString "(" <<< showsPrec d x
    <<< showString " , " <<< showsPrec d y <<< showString ")"

  Show-Either : {{Show a}} -> {{Show b}} -> Show (Either a b)
  Show-Either .showsPrec d = \ where
    (left x) -> showParen (d > appPrec)
      (showString "Left " <<< showsPrec appPrec+1 x)
    (right x) -> showParen (d > appPrec)
      (showString "Right " <<< showsPrec appPrec+1 x)

  Show-Maybe : {{Show a}} -> Show (Maybe a)
  Show-Maybe .showsPrec d = \ where
    (just x) -> showParen (d > appPrec)
      (showString "Just " <<< showsPrec appPrec+1 x)
    nothing -> showString "nothing"

  Show-List : {{Show a}} -> Show (List a)
  Show-List .showsPrec _ [] = showString "[]"
  Show-List .showsPrec d (x :: xs) =
      showString "[" <<< content <<< showString "]"
    where
      content : ShowS
      content = showsPrec d x <<< go xs
        where
          go : {{Show a}} -> List a -> ShowS
          go [] = showString ""
          go (y :: ys) = showString ", " <<< showsPrec d y <<< go ys
