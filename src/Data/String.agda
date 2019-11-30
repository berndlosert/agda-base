{-# OPTIONS --type-in-type #-}

module Data.String where

open import Agda.Builtin.FromString public
open import Agda.Builtin.String public
open import Data.Bool
open import Data.Cast
open import Data.Char
open import Data.Decimal
open import Data.Eq public
open import Data.Function
open import Data.List
open import Data.Maybe
open import Data.Monoid
open import Data.Nat.Base
open import Data.Semigroup
open import Data.Unit public
open import Notation.Append public

instance
  -- This is how we compare strings for equality.
  Eq:String : Eq String
  Eq:String = Eq: primStringEquality

  -- Use ++ to append strings.
  Append:String : Append String
  Append:String = Append: primStringAppend

  -- We need to define an IsString String instance if we're going to use
  -- IsString.
  IsString:String : IsString String
  IsString:String = record {
      Constraint = \ _ -> Unit;
      fromString = \ s -> s
    }

  -- String is a semigroup.
  Semigroup:String : Semigroup String
  Semigroup:String = Semigroup: _++_

  -- String is a monoid.
  Monoid:String : Monoid String
  Monoid:String = Monoid: ""

  -- Cast String to List Char.
  StringToList : Cast String (List Char)
  StringToList = Cast: primStringToList

  -- Cast List Char to String.
  StringFromList : Cast (List Char) String
  StringFromList = Cast: primStringFromList

  -- Cast Char to String.
  CharToString : Cast Char String
  CharToString = Cast: \ c -> primStringFromList [ c ]

  -- Parse a natural number string into a natural number.
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

postulate
  startsWith : String -> String -> Bool
  stripPrefix : String -> String -> Maybe String
  length : String -> Nat

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC startsWith = Text.isPrefixOf #-}
{-# COMPILE GHC stripPrefix = Text.stripPrefix #-}
{-# COMPILE GHC length = toInteger . Text.length #-}

padRight : Nat -> Char -> String -> String
padRight desiredLength padChar s =
  s ++ (foldl _++_ "" (replicate (desiredLength - length s) (cast padChar)))

padLeft : Nat -> Char -> String -> String
padLeft desiredLength padChar s =
  (foldl _++_ "" (replicate (desiredLength - length s) (cast padChar))) ++ s
