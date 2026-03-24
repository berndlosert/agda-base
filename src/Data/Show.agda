module Data.Show where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.String.Builder as Builder using (Builder)

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
  showChar = Builder.singleton

  showString : String -> ShowS
  showString = Builder.toBuilder

  fromShowS : ShowS -> String
  fromShowS = Builder.fromBuilder

  instance
    Semigroup-ShowS : Semigroup ShowS
    Semigroup-ShowS = Builder.Semigroup-Builder

    Monoid-ShowS : Monoid ShowS
    Monoid-ShowS = Builder.Monoid-Builder

    FromString-ShowS : FromString ShowS
    FromString-ShowS = Builder.FromString-Builder

    FromString-Constraint-ShowS : {s : String} -> FromString.Constraint FromString-ShowS s
    FromString-Constraint-ShowS = _

-------------------------------------------------------------------------------
-- Show
-------------------------------------------------------------------------------

record Show (a : Type) : Type where
  field
    show : a -> String
    showsPrec : Nat -> a -> ShowS

open Show {{...}} public

module _ {{_ : Show a}} where
  shows : a -> ShowS
  shows = showsPrec 0

  showDefault : a -> String
  showDefault = fromShowS <<< shows

  showsPrecDefault : Nat -> a -> ShowS
  showsPrecDefault _ = showString <<< show

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
