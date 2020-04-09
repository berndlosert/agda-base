{-# OPTIONS --type-in-type #-}

module Data.Char where

open import Data.Eq
open import Data.Nat

open import Agda.Builtin.Char public
  using (Char)
  renaming (
    primIsLower to isLower;
    primIsDigit to isDigit;
    primIsAlpha to isAlpha;
    primIsSpace to isSpace;
    primIsAscii to isAscii;
    primIsLatin1 to isLatin1;
    primIsPrint to isPrint;
    primIsHexDigit to isHexDigit;
    primToUpper to toUpper;
    primToLower to toLower;
    primCharToNat to ord;
    primNatToChar to chr
  )

fromDecDigit : Char -> Nat
fromDecDigit = \ where
  '0' -> 0
  '1' -> 1
  '2' -> 2
  '3' -> 3
  '4' -> 4
  '5' -> 5
  '6' -> 6
  '7' -> 7
  '8' -> 8
  '9' -> 9
  _ -> 0

instance
  eqChar : Eq Char
  eqChar ._==_ c d = ord c == ord d
