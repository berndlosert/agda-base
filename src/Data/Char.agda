{-# OPTIONS --type-in-type #-}

module Data.Char where

module Char where
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

open Char public
  using (Char)

open import Data.Nat

open import Prelude

instance
  eqChar : Eq Char
  eqChar ._==_ c d = Char.ord c == Char.ord d
