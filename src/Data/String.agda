{-# OPTIONS --type-in-type #-}

module Data.String where

-- String is just Text from Haskell.

open import Agda.Builtin.FromString public
open import Agda.Builtin.String public

-- This is how we compare strings for equality.

open import Data.Eq public

instance
  Eq:String : Eq String
  Eq:String = Eq: primStringEquality

-- Use ++ to append strings.

open import Notation.Append public

instance
  Append:String : Append String
  Append:String = Append: primStringAppend

-- We need to define an IsString String instance if we're going to use
-- IsString.

open import Data.Unit public

instance
  IsString:String : IsString String
  IsString:String = record {
      Constraint = \ _ -> Unit;
      fromString = \ s -> s
    }

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

-- Cast String to List Char.

open import Data.Cast
open import Data.Char
open import Data.List.Base

instance
  StringToList : Cast String (List Char)
  StringToList = Cast: primStringToList

-- Cast List Char to String.

instance
  StringFromList : Cast (List Char) String
  StringFromList = Cast: primStringFromList

-- Cast Char to String.

instance
  CharToString : Cast Char String
  CharToString = Cast: \ c -> primStringFromList [ c ]

-- Parse a natural number string into a natural number.

open import Data.Decimal
open import Data.Function
open import Data.Maybe
open import Data.Nat.Base

instance
  StringToNat : Cast String (Maybe Nat)
  StringToNat .cast str =
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
