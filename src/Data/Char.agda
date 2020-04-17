{-# OPTIONS --type-in-type #-}

module Data.Char where

open import Agda.Builtin.Char public
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

open import Data.Eq
open import Data.Nat
open import Prim

instance
  eqChar : Eq Char
  eqChar ._==_ c d = ord c == ord d
