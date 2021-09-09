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

toDigit : Char -> Maybe Nat
toDigit '0' = just 0
toDigit '1' = just 1
toDigit '2' = just 2
toDigit '3' = just 3
toDigit '4' = just 4
toDigit '5' = just 5
toDigit '6' = just 6
toDigit '7' = just 7
toDigit '8' = just 8
toDigit '9' = just 9
toDigit _ = nothing

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
