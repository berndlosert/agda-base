*********
Data.Char
*********
::

  {-# OPTIONS --type-in-type #-}

  module Data.Char where

``Char`` is the set of characters that you can type into your computer::

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

This function will convert a char digit into its corresponding natural number::

  open import Data.Bool
  open import Data.Nat.Base

  digitToNat : (c : Char) → {_ : Constraint (isDigit c)} → Nat
  digitToNat c = ord c - ord '0'

This is the ``Maybe`` version of the above operation::

  open import Data.Maybe

  digitToNat? : (c : Char) → Maybe Nat
  digitToNat? c = if isDigit c then just (ord c - ord '0') else nothing
