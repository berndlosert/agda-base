{-# OPTIONS --type-in-type #-}

module Data.Char where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Agda.Builtin.Char

-------------------------------------------------------------------------------
-- Char primitives
-------------------------------------------------------------------------------

minChar maxChar : Char
minChar = '\NUL'
maxChar = '\1114111'

isLower : Char -> Bool
isLower = primIsLower

isDigit : Char -> Bool
isDigit = primIsDigit

isAlpha : Char -> Bool
isAlpha = primIsAlpha

isSpace : Char -> Bool
isSpace = primIsSpace

isAscii : Char -> Bool
isAscii = primIsAscii

isLatin1 : Char -> Bool
isLatin1 = primIsLatin1

isPrint : Char -> Bool
isPrint = primIsPrint

isHexDigit : Char -> Bool
isHexDigit = primIsHexDigit

toUpper : Char -> Char
toUpper = primToUpper

toLower : Char -> Char
toLower = primToLower

ord : Char -> Nat
ord = primCharToNat

chr : Nat -> Char
chr n = primNatToChar $ min n (ord maxChar)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Eq-Char : Eq Char
  Eq-Char ._==_ = primCharEquality

  Ord-Char : Ord Char
  Ord-Char .compare l r = compare (ord l) (ord r)
