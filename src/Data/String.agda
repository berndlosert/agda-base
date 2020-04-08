{-# OPTIONS --type-in-type #-}

module Data.String where

open import Agda.Builtin.String public
  using (String)
  renaming (
    primStringToList to unpack;
    primStringFromList to pack
    --primStringAppend to append
  )

  --open import Data.Char public
  --open import Data.Sequence
  --open import Data.List
  --open import Data.Nat

open import Data.Char public
open import Data.Function
open import Data.Eq
open import Data.List
open import Data.Monoid
open import Data.Sequence

instance
  eqString : Eq String
  eqString ._==_ = Agda.Builtin.String.primStringEquality

  semigroupString : Semigroup String
  semigroupString ._<>_ = Agda.Builtin.String.primStringAppend

  monoidString : Monoid String
  monoidString .mempty = ""

  foldStringChar : Fold String Char
  foldStringChar .foldMap f = foldMap f <<< unpack

  sequenceStringChar : Sequence String Char
  sequenceStringChar .nil = ""
  sequenceStringChar .cons c s = pack (c :: unpack s)

  --padRight : Nat -> Char -> String -> String
  --padRight desiredLength padChar s =
  --  let replicated = List.replicate (desiredLength - length s) (fromChar padChar)
  --  in s ++ (List.foldl _++_ "" replicated)
  --
  --padLeft : Nat -> Char -> String -> String
  --padLeft desiredLength padChar s =
  --  let replicated = List.replicate (desiredLength - length s) (fromChar padChar)
  --  in (List.foldl _++_ "" replicated) ++ s

  --{-# FOREIGN GHC import qualified Data.Text as Text #-}
  --{-# COMPILE GHC length = toInteger . Text.length #-}
  --{-# COMPILE GHC startsWith = Text.isPrefixOf #-}
  --{-# COMPILE GHC stripPrefix = Text.stripPrefix #-}
  --{-# COMPILE GHC uncons = Text.uncons #-}
  --{-# COMPILE GHC cons = Text.cons #-}
  --{-# COMPILE GHC takeWhile = Text.takeWhile #-}
  --{-# COMPILE GHC dropWhile = Text.dropWhile #-}


