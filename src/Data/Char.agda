{-# OPTIONS --type-in-type #-}

module Data.Char where

open import Data.Eq using (Eq)
open import Data.Eq public using (_==_; _/=_)
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

instance
  eqChar : Eq Char
  eqChar ._==_ c d = let ord = Agda.Builtin.Char.primCharToNat in
    ord c == ord d
