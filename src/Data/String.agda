{-# OPTIONS --type-in-type #-}

module Data.String where

open import Data.String.Base public

module String where

  -- Functions for converting String to/from List Char.

  open import Agda.Builtin.String as Builtin

  toList = Builtin.primStringToList
  fromList = Builtin.primStringFromList
  show = Builtin.primShowString

  -- Convert a Char to a String.

  open import Data.Char
  open import Data.List

  fromChar : Char -> String
  fromChar c = fromList (pure c)

  -- Parse a natural number string into a natural number.

  open import Data.Digit
  open import Data.Decimal
  open import Data.Function
  open import Data.Traversable
  open import Data.Maybe
  open import Data.Nat

  parseDecimal : String -> Maybe Decimal
  parseDecimal = toList >>> List.reverse >>> traverse Digit.fromChar

  parseNat : String -> Maybe Nat
  parseNat str =
      case (parseDecimal str)  of \ where
        nothing -> nothing
        (just x) -> just (Decimal.toNat x)

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

  open import Data.List

  padRight : Nat -> Char -> String -> String
  padRight desiredLength padChar s =
    let replicated = List.replicate (desiredLength - length s) (fromChar padChar)
    in s ++ (foldl _++_ "" replicated)

  padLeft : Nat -> Char -> String -> String
  padLeft desiredLength padChar s =
    let replicated = List.replicate (desiredLength - length s) (fromChar padChar)
    in (foldl _++_ "" replicated) ++ s

  -- Concatenate a list of strings into one string.

  concat : List String -> String
  concat [] = ""
  concat (str :: strs) = str ++ concat strs
