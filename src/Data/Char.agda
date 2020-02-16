{-# OPTIONS --type-in-type #-}

module Data.Char where

-- The type Char of characters that you can type into your computer.

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

-- With this instance we can compare Char values for equality.

open import Data.Eq public
open import Data.Nat

instance
  Eq:Char : Eq Char
  Eq:Char ._==_ c c' = ord c == ord c'
