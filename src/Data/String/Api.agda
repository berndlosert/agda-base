{-# OPTIONS --type-in-type #-}

module Data.String.Api where

open import Data.String.Base

-- String is a semigroup.

open import Data.Semigroup

instance
  Semigroup:String : Semigroup String
  Semigroup:String = Semigroup: _++_

-- String is a monoid.

open import Data.Monoid

instance
  Monoid:String : Monoid String
  Monoid:String = Monoid: ""

-- Functions for converting String to/from List Char.

open import Agda.Builtin.String
  using (primStringToList; primStringFromList)

toList = primStringToList
fromList = primStringFromList

-- Convert a Char to a String. 

open import Data.Char
open import Data.List

toChar : Char -> String
toChar c = fromList [ c ]

-- Parse a natural number string into a natural number.

open import Data.Decimal
open import Data.Function
open import Data.Maybe
open import Data.Nat.Base

parseNat : String -> Maybe Nat
parseNat str =
  let
    decimal? : Maybe Decimal
    decimal? = str
      & cast {String} {List Char}
      & cast {List Char} {Maybe Decimal}
  in
    case decimal? of \ where
      nothing -> nothing
      (just x) -> just (cast {Decimal} {Nat} x)

-- Import the following functions from Haskell.

open import Data.Bool

postulate
  startsWith : String -> String -> Bool
  stripPrefix : String -> String -> Maybe String
  length : String -> Nat

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC startsWith = Text.isPrefixOf #-}
{-# COMPILE GHC stripPrefix = Text.stripPrefix #-}
{-# COMPILE GHC length = toInteger . Text.length #-}

-- Pad a string with a character up to some desired length.

import Data.List as List

padRight : Nat -> Char -> String -> String
padRight desiredLength padChar s =
  let replicated = List.replicate (desiredLength - length s) (cast padChar)
  in s ++ (List.foldl _++_ "" replicated)

padLeft : Nat -> Char -> String -> String
padLeft desiredLength padChar s =
  let replicated = List.replicate (desiredLength - length s) (cast padChar)
  in (List.foldl _++_ "" replicated) ++ s

-- Concatenate a list of strings into one string. 

concat : List String -> String
concat [] = ""
concat (str :: strs) = str ++ concat strs
